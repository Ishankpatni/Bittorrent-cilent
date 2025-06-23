package main

// Combined imports from all packages
import (
	"bytes"
	"context"
	"crypto/rand"
	"crypto/sha1"
	"encoding/binary"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"time"

	"fyne.io/fyne/v2"
	"fyne.io/fyne/v2/app"
	"fyne.io/fyne/v2/container"
	"fyne.io/fyne/v2/data/binding"
	"fyne.io/fyne/v2/dialog"
	"fyne.io/fyne/v2/storage"
	"fyne.io/fyne/v2/theme"
	"fyne.io/fyne/v2/widget"

	"torrent-client/seeding"

	"github.com/jackpal/bencode-go"
)

// --- From bitfield.go ---
// Bitfield represents the pieces that a peer has
type Bitfield []byte

// HasPiece tells if a bitfield has a particular index set
func (bf Bitfield) HasPiece(index int) bool {
	byteIndex := index / 8
	offset := index % 8
	if byteIndex < 0 || byteIndex >= len(bf) {
		return false
	}
	return bf[byteIndex]>>uint(7-offset)&1 != 0
}

// SetPiece sets a bit in the bitfield
func (bf Bitfield) SetPiece(index int) {
	byteIndex := index / 8
	offset := index % 8

	if byteIndex < 0 || byteIndex >= len(bf) {
		// This could happen if the bitfield is not pre-sized correctly or a peer sends an invalid HAVE.
		// For simplicity, we're not growing the bitfield here.
		// log.Printf("Warning: SetPiece out of bounds. Index: %d, Bitfield len: %d bytes. Peer might be misbehaving.", index, len(bf))
		return
	}
	bf[byteIndex] |= 1 << uint(7-offset)
}

// --- From handshake.go ---
// Handshake is a special message that a peer uses to identify itself
type Handshake struct {
	Pstr     string
	InfoHash [20]byte
	PeerID   [20]byte
}

// NewHandshake creates a new handshake with the standard pstr
func NewHandshake(infoHash, peerID [20]byte) *Handshake {
	return &Handshake{
		Pstr:     "BitTorrent protocol",
		InfoHash: infoHash,
		PeerID:   peerID,
	}
}

// Serialize serializes the handshake to a buffer
func (h *Handshake) Serialize() []byte {
	buf := make([]byte, len(h.Pstr)+49)
	buf[0] = byte(len(h.Pstr))
	curr := 1
	curr += copy(buf[curr:], h.Pstr)
	curr += copy(buf[curr:], make([]byte, 8)) // 8 reserved bytes
	curr += copy(buf[curr:], h.InfoHash[:])
	curr += copy(buf[curr:], h.PeerID[:])
	return buf
}

// ReadHandshake parses a handshake from a stream
func ReadHandshake(r io.Reader) (*Handshake, error) {
	lengthBuf := make([]byte, 1)
	_, err := io.ReadFull(r, lengthBuf)
	if err != nil {
		return nil, err
	}
	pstrlen := int(lengthBuf[0])

	if pstrlen == 0 {
		return nil, fmt.Errorf("pstrlen cannot be 0")
	}
	// Standard pstrlen is 19 for "BitTorrent protocol"
	if pstrlen > 255 { // Theoretical max, practical max much lower
		return nil, fmt.Errorf("pstrlen too large: %d", pstrlen)
	}

	handshakeBuf := make([]byte, 48+pstrlen)
	_, err = io.ReadFull(r, handshakeBuf)
	if err != nil {
		return nil, err
	}

	var infoHash, peerID [20]byte

	copy(infoHash[:], handshakeBuf[pstrlen+8:pstrlen+8+20])
	copy(peerID[:], handshakeBuf[pstrlen+8+20:])

	h := Handshake{
		Pstr:     string(handshakeBuf[0:pstrlen]),
		InfoHash: infoHash,
		PeerID:   peerID,
	}

	return &h, nil
}

// --- From message.go ---
type messageID uint8

const (
	MsgChoke         messageID = 0
	MsgUnchoke       messageID = 1
	MsgInterested    messageID = 2
	MsgNotInterested messageID = 3
	MsgHave          messageID = 4
	MsgBitfield      messageID = 5
	MsgRequest       messageID = 6
	MsgPiece         messageID = 7
	MsgCancel        messageID = 8
)

// Message stores ID and payload of a message
type Message struct {
	ID      messageID
	Payload []byte
}

// FormatRequest creates a REQUEST message
func FormatRequest(index, begin, length int) *Message {
	payload := make([]byte, 12)
	binary.BigEndian.PutUint32(payload[0:4], uint32(index))
	binary.BigEndian.PutUint32(payload[4:8], uint32(begin))
	binary.BigEndian.PutUint32(payload[8:12], uint32(length))
	return &Message{ID: MsgRequest, Payload: payload}
}

// FormatHave creates a HAVE message
func FormatHave(index int) *Message {
	payload := make([]byte, 4)
	binary.BigEndian.PutUint32(payload, uint32(index))
	return &Message{ID: MsgHave, Payload: payload}
}

// ParsePiece parses a PIECE message and copies its payload into a buffer
func ParsePiece(index int, buf []byte, msg *Message) (int, error) {
	if msg.ID != MsgPiece {
		return 0, fmt.Errorf("expected PIECE (ID %d), got ID %d", MsgPiece, msg.ID)
	}
	if len(msg.Payload) < 8 { // Must have index and begin
		return 0, fmt.Errorf("payload too short for PIECE message. Length %d < 8", len(msg.Payload))
	}
	parsedIndex := int(binary.BigEndian.Uint32(msg.Payload[0:4]))
	if parsedIndex != index {
		return 0, fmt.Errorf("expected piece index %d, got %d", index, parsedIndex)
	}
	begin := int(binary.BigEndian.Uint32(msg.Payload[4:8]))
	if begin >= len(buf) { // begin offset must be within the piece buffer
		return 0, fmt.Errorf("begin offset %d too high for piece buffer of size %d", begin, len(buf))
	}
	data := msg.Payload[8:]
	if begin+len(data) > len(buf) {
		return 0, fmt.Errorf("data too long for piece buffer. Data len %d, offset %d, buffer len %d", len(data), begin, len(buf))
	}
	copy(buf[begin:], data)
	return len(data), nil
}

// ParseHave parses a HAVE message
func ParseHave(msg *Message) (int, error) {
	if msg.ID != MsgHave {
		return 0, fmt.Errorf("expected HAVE (ID %d), got ID %d", MsgHave, msg.ID)
	}
	if len(msg.Payload) != 4 {
		return 0, fmt.Errorf("expected HAVE payload length 4, got length %d", len(msg.Payload))
	}
	index := int(binary.BigEndian.Uint32(msg.Payload))
	return index, nil
}

// Serialize serializes a message into a buffer of the form
// <length prefix><message ID><payload>
// Interprets `nil` as a keep-alive message
func (m *Message) Serialize() []byte {
	if m == nil {
		return make([]byte, 4) // Keep-alive: 4 bytes of zero
	}
	length := uint32(len(m.Payload) + 1) // +1 for message ID
	buf := make([]byte, 4+length)        // 4 for length prefix
	binary.BigEndian.PutUint32(buf[0:4], length)
	buf[4] = byte(m.ID)
	copy(buf[5:], m.Payload)
	return buf
}

// ReadMessage parses a message from a stream. Returns `nil` on keep-alive message
func ReadMessage(r io.Reader) (*Message, error) {
	lengthBuf := make([]byte, 4)
	_, err := io.ReadFull(r, lengthBuf)
	if err != nil {
		return nil, err
	}
	length := binary.BigEndian.Uint32(lengthBuf)

	if length == 0 { // keep-alive message
		return nil, nil
	}
	if length > MaxBlockSize*2 { // Sanity check for message length (max piece/block + overhead)
		return nil, fmt.Errorf("message length %d too large", length)
	}

	messageBuf := make([]byte, length)
	_, err = io.ReadFull(r, messageBuf)
	if err != nil {
		return nil, err
	}

	m := Message{
		ID:      messageID(messageBuf[0]),
		Payload: messageBuf[1:],
	}
	return &m, nil
}

func (m *Message) name() string {
	if m == nil {
		return "KeepAlive"
	}
	switch m.ID {
	case MsgChoke:
		return "Choke"
	case MsgUnchoke:
		return "Unchoke"
	case MsgInterested:
		return "Interested"
	case MsgNotInterested:
		return "NotInterested"
	case MsgHave:
		return "Have"
	case MsgBitfield:
		return "Bitfield"
	case MsgRequest:
		return "Request"
	case MsgPiece:
		return "Piece"
	case MsgCancel:
		return "Cancel"
	default:
		return fmt.Sprintf("Unknown#%d", m.ID)
	}
}

func (m *Message) String() string {
	if m == nil {
		return m.name()
	}
	return fmt.Sprintf("%s [PayloadLen:%d]", m.name(), len(m.Payload))
}

// --- From peers.go ---
// Peer encodes connection information for a peer
type Peer struct {
	IP   net.IP
	Port uint16
}

// UnmarshalPeers parses peer IP addresses and ports from a buffer (compact format)
func UnmarshalPeers(peersBin []byte) ([]Peer, error) {
	const peerSize = 6 // 4 bytes for IP, 2 bytes for port
	if len(peersBin)%peerSize != 0 {
		return nil, fmt.Errorf("received malformed peers data (length %d is not a multiple of %d)", len(peersBin), peerSize)
	}
	numPeers := len(peersBin) / peerSize
	peers := make([]Peer, numPeers)
	for i := 0; i < numPeers; i++ {
		offset := i * peerSize
		peers[i].IP = net.IP(peersBin[offset : offset+4])
		peers[i].Port = binary.BigEndian.Uint16(peersBin[offset+4 : offset+6])
	}
	return peers, nil
}

func (p Peer) String() string {
	return net.JoinHostPort(p.IP.String(), strconv.Itoa(int(p.Port)))
}

// --- From client.go ---
// PeerClient is a TCP connection with a peer (renamed from client.Client)
type PeerClient struct {
	Conn      net.Conn
	Choked    bool     // We are choked by the peer
	AmChoking bool     // We are choking the peer (not used by this client logic, but good to note)
	Bitfield  Bitfield // Peer's bitfield
	peer      Peer
	infoHash  [20]byte
	peerID    [20]byte // Our peer ID
}

func completePeerHandshake(conn net.Conn, infohash, localPeerID [20]byte) (*Handshake, error) {
	conn.SetDeadline(time.Now().Add(5 * time.Second)) // Increased timeout slightly
	defer conn.SetDeadline(time.Time{})               // Disable the deadline

	req := NewHandshake(infohash, localPeerID)
	_, err := conn.Write(req.Serialize())
	if err != nil {
		return nil, fmt.Errorf("failed to send handshake: %w", err)
	}

	res, err := ReadHandshake(conn)
	if err != nil {
		return nil, fmt.Errorf("failed to read handshake response: %w", err)
	}
	if !bytes.Equal(res.InfoHash[:], infohash[:]) {
		return nil, fmt.Errorf("expected infohash %x but got %x", infohash, res.InfoHash)
	}
	// Note: We don't typically check res.PeerID against anything specific at this stage,
	// but it's good to have if we want to track peer IDs.
	return res, nil
}

func recvPeerBitfield(conn net.Conn, numPieces int) (Bitfield, error) {
	conn.SetDeadline(time.Now().Add(10 * time.Second)) // Increased timeout
	defer conn.SetDeadline(time.Time{})                // Disable the deadline

	// Loop to handle potential keep-alives before bitfield
	for i := 0; i < 5; i++ { // Try a few times to get past keep-alives
		msg, err := ReadMessage(conn)
		if err != nil {
			return nil, fmt.Errorf("error reading initial message (expected bitfield): %w", err)
		}
		if msg == nil { // Keep-alive
			// log.Printf("Received keep-alive before bitfield from %s", conn.RemoteAddr())
			continue
		}
		if msg.ID != MsgBitfield {
			// Some clients might send HAVE messages if they only have a few pieces.
			// A more robust client would handle these. For now, strict expectation.
			// log.Printf("Expected bitfield from %s but got ID %d (%s). Payload: %x", conn.RemoteAddr(), msg.ID, msg.name(), msg.Payload)
			return nil, fmt.Errorf("expected bitfield but got message ID %d (%s)", msg.ID, msg.name())
		}

		// Validate bitfield length
		expectedBitfieldLen := (numPieces + 7) / 8
		if len(msg.Payload) != expectedBitfieldLen {
			return nil, fmt.Errorf("bitfield length mismatch: expected %d, got %d for %d pieces",
				expectedBitfieldLen, len(msg.Payload), numPieces)
		}
		return msg.Payload, nil
	}
	return nil, fmt.Errorf("did not receive bitfield after multiple attempts (possibly too many keep-alives)")
}

// NewPeerClient connects with a peer, completes a handshake, and receives a bitfield
func NewPeerClient(peer Peer, localPeerID, infoHash [20]byte, numPieces int) (*PeerClient, error) {
	conn, err := net.DialTimeout("tcp", peer.String(), 5*time.Second) // Increased Dial timeout
	if err != nil {
		return nil, fmt.Errorf("failed to dial peer %s: %w", peer.String(), err)
	}

	_, err = completePeerHandshake(conn, infoHash, localPeerID)
	if err != nil {
		conn.Close()
		return nil, fmt.Errorf("handshake with %s failed: %w", peer.String(), err)
	}

	bf, err := recvPeerBitfield(conn, numPieces)
	if err != nil {
		conn.Close()
		return nil, fmt.Errorf("failed to receive bitfield from %s: %w", peer.String(), err)
	}

	return &PeerClient{
		Conn:     conn,
		Choked:   true, // Assume choked by default, peer will send Unchoke
		Bitfield: bf,
		peer:     peer,
		infoHash: infoHash,
		peerID:   localPeerID,
	}, nil
}

// Read reads and consumes a message from the connection
func (pc *PeerClient) Read() (*Message, error) {
	if pc.Conn == nil {
		return nil, fmt.Errorf("connection is nil")
	}
	msg, err := ReadMessage(pc.Conn)
	return msg, err
}

// SendRequest sends a Request message to the peer
func (pc *PeerClient) SendRequest(index, begin, length int) error {
	if pc.Conn == nil {
		return fmt.Errorf("connection is nil")
	}
	req := FormatRequest(index, begin, length)
	_, err := pc.Conn.Write(req.Serialize())
	return err
}

// SendInterested sends an Interested message to the peer
func (pc *PeerClient) SendInterested() error {
	if pc.Conn == nil {
		return fmt.Errorf("connection is nil")
	}
	msg := Message{ID: MsgInterested}
	_, err := pc.Conn.Write(msg.Serialize())
	return err
}

// SendNotInterested sends a NotInterested message to the peer
func (pc *PeerClient) SendNotInterested() error {
	if pc.Conn == nil {
		return fmt.Errorf("connection is nil")
	}
	msg := Message{ID: MsgNotInterested}
	_, err := pc.Conn.Write(msg.Serialize())
	return err
}

// SendUnchoke sends an Unchoke message to the peer (if we were choking them)
func (pc *PeerClient) SendUnchoke() error {
	if pc.Conn == nil {
		return fmt.Errorf("connection is nil")
	}
	msg := Message{ID: MsgUnchoke}
	_, err := pc.Conn.Write(msg.Serialize())
	if err == nil {
		pc.AmChoking = false
	}
	return err
}

// SendHave sends a Have message to the peer
func (pc *PeerClient) SendHave(index int) error {
	if pc.Conn == nil {
		return fmt.Errorf("connection is nil")
	}
	msg := FormatHave(index)
	_, err := pc.Conn.Write(msg.Serialize())
	return err
}

// --- From torrentfile.go ---
// (Used to be TorrentFile, renamed to TorrentMetadata to avoid clash with p2p.Torrent)
// TorrentMetadata encodes the metadata from a .torrent file
type TorrentMetadata struct {
	AnnounceList [][]string // For supporting multiple trackers (tiers of trackers)
	Announce     string     // Single primary tracker URL
	InfoHash     [20]byte
	PieceHashes  [][20]byte // Slice of 20-byte SHA1 hashes
	PieceLength  int
	Length       int           // Total length of all files
	Name         string        // Suggested name (directory for multi-file, filename for single)
	Files        []BencodeFile // For multi-file torrents
	IsSingleFile bool
}

// BencodeFile represents a file in a multi-file torrent
type BencodeFile struct {
	Length int      `bencode:"length"`
	Path   []string `bencode:"path"` // Path components relative to torrent root
}

// bencodeInfo is the structure of the 'info' dictionary in a .torrent file
type bencodeInfo struct {
	Pieces      string        `bencode:"pieces"` // Concatenated SHA1 hashes
	PieceLength int           `bencode:"piece length"`
	Name        string        `bencode:"name"`
	Length      int           `bencode:"length,omitempty"`  // For single file torrent
	Files       []BencodeFile `bencode:"files,omitempty"`   // For multi-file torrent
	Private     int           `bencode:"private,omitempty"` // Optional: 1 for private torrent
	// Other optional fields like 'source' could be here
}

// bencodeTorrent is the top-level structure of a .torrent file
type bencodeTorrent struct {
	Announce     string      `bencode:"announce"`
	AnnounceList [][]string  `bencode:"announce-list,omitempty"`
	Info         bencodeInfo `bencode:"info"`
	Comment      string      `bencode:"comment,omitempty"`
	CreatedBy    string      `bencode:"created by,omitempty"`
	CreationDate int64       `bencode:"creation date,omitempty"`
	// Encoding     string        `bencode:"encoding,omitempty"` // Typically UTF-8
}

// OpenTorrentFile parses a torrent file from the given path
func OpenTorrentFile(path string) (*TorrentMetadata, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, fmt.Errorf("failed to open torrent file %s: %w", path, err)
	}
	defer file.Close()

	bto := bencodeTorrent{}
	err = bencode.Unmarshal(file, &bto)
	if err != nil {
		return nil, fmt.Errorf("failed to bdecode torrent file %s: %w", path, err)
	}
	return btoToTorrentMetadata(&bto)
}

// hash calculates the SHA1 hash of the bencoded 'info' dictionary
func (i *bencodeInfo) hash() ([20]byte, error) {
	var buf bytes.Buffer
	err := bencode.Marshal(&buf, *i)
	if err != nil {
		return [20]byte{}, fmt.Errorf("failed to bencode info dict for hashing: %w", err)
	}
	return sha1.Sum(buf.Bytes()), nil
}

// splitPieceHashes splits the concatenated piece hashes string into a slice of [20]byte arrays
func (i *bencodeInfo) splitPieceHashes() ([][20]byte, error) {
	hashLen := 20 // SHA-1 hash length
	buf := []byte(i.Pieces)
	if len(buf)%hashLen != 0 {
		return nil, fmt.Errorf("malformed pieces string: length %d is not a multiple of %d", len(buf), hashLen)
	}
	numHashes := len(buf) / hashLen
	if numHashes == 0 && i.Length > 0 { // If there's data, there must be pieces
		return nil, fmt.Errorf("no piece hashes found but torrent has length %d", i.Length)
	}
	hashes := make([][20]byte, numHashes)
	for j := 0; j < numHashes; j++ {
		copy(hashes[j][:], buf[j*hashLen:(j+1)*hashLen])
	}
	return hashes, nil
}

// btoToTorrentMetadata converts the bdecoded structure to our TorrentMetadata format
func btoToTorrentMetadata(bto *bencodeTorrent) (*TorrentMetadata, error) {
	if bto.Info.PieceLength <= 0 {
		return nil, fmt.Errorf("invalid piece length: %d", bto.Info.PieceLength)
	}

	infoHash, err := bto.Info.hash()
	if err != nil {
		return nil, err
	}
	pieceHashes, err := bto.Info.splitPieceHashes()
	if err != nil {
		return nil, err
	}

	tm := &TorrentMetadata{
		Announce:     bto.Announce,
		AnnounceList: bto.AnnounceList,
		InfoHash:     infoHash,
		PieceHashes:  pieceHashes,
		PieceLength:  bto.Info.PieceLength,
		Name:         bto.Info.Name, // This is often the suggested filename or directory name
	}

	if len(bto.Info.Files) > 0 { // Multi-file torrent
		tm.IsSingleFile = false
		tm.Files = bto.Info.Files
		if tm.Name == "" && len(tm.Files) > 0 { // If root name is empty, try to use first file's path as hint
			tm.Name = tm.Files[0].Path[0]
		}
		var totalLength int
		for _, f := range tm.Files {
			if f.Length < 0 {
				return nil, fmt.Errorf("invalid file length in multi-file torrent: %d", f.Length)
			}
			totalLength += f.Length
		}
		tm.Length = totalLength
	} else { // Single-file torrent
		tm.IsSingleFile = true
		if bto.Info.Length < 0 {
			return nil, fmt.Errorf("invalid torrent length for single file: %d", bto.Info.Length)
		}
		tm.Length = bto.Info.Length
		// For single file torrent, bencodeInfo.Name is the filename.
		// Create a BencodeFile entry for consistency in handling.
		tm.Files = []BencodeFile{{Length: tm.Length, Path: []string{tm.Name}}}
	}

	if tm.Length == 0 && len(pieceHashes) > 0 { // Torrent reports length 0 but has pieces
		// This can happen for torrents that only announce hashes (e.g. magnet links initially)
		// but if opened from a file, length should generally be non-zero if pieces exist.
		// log.Printf("Warning: Torrent %s has 0 total length but %d piece hashes.", tm.Name, len(pieceHashes))
	}
	if tm.Length > 0 && len(pieceHashes) == 0 {
		return nil, fmt.Errorf("torrent %s has length %d but 0 piece hashes", tm.Name, tm.Length)
	}

	return tm, nil
}

// --- Tracker Communication (HTTP) ---
// OurClientPort is the port our client listens on (or claims to) for incoming connections
const OurClientPort uint16 = 19091 // Changed to 19091 as per requirements

// bencodeTrackerResp is the structure for bdecoded tracker HTTP responses
type bencodeTrackerResp struct {
	Interval       int    `bencode:"interval"`                 // Advised seconds between regular tracker requests
	MinInterval    int    `bencode:"min interval,omitempty"`   // Minimum advised interval
	Peers          string `bencode:"peers"`                    // Compact peer list (binary model)
	Peers6         string `bencode:"peers6,omitempty"`         // Compact IPv6 peer list
	FailureReason  string `bencode:"failure reason,omitempty"` // If request failed
	WarningMessage string `bencode:"warning message,omitempty"`
	Complete       int    `bencode:"complete,omitempty"`   // Number of seeders
	Incomplete     int    `bencode:"incomplete,omitempty"` // Number of leechers
	TrackerId      string `bencode:"tracker id,omitempty"` // Returned by tracker, to be sent in subsequent requests
}

// GetPeers retrieves peer information from the tracker
func (tm *TorrentMetadata) GetPeers(localPeerID [20]byte, port uint16, downloaded, uploaded, left int) ([]Peer, int, error) {
	// Try the primary announce URL first
	peers, interval, err := tm.requestPeersFromSingleTracker(tm.Announce, localPeerID, port, downloaded, uploaded, left)
	if err != nil {
		log.Printf("Failed to get peers from primary tracker %s: %v", tm.Announce, err)
		return nil, 0, err
	}

	return peers, interval, nil
}

func (tm *TorrentMetadata) requestPeersFromSingleTracker(
	announceURL string, localPeerID [20]byte, port uint16,
	downloaded, uploaded, left int,
) ([]Peer, int, error) {
	base, err := url.Parse(announceURL)
	if err != nil {
		return nil, 0, fmt.Errorf("malformed tracker URL '%s': %w", announceURL, err)
	}

	// Handle UDP trackers
	if base.Scheme == "udp" {
		return tm.requestPeersFromUDPTracker(announceURL, localPeerID, port, downloaded, uploaded, left)
	}

	// HTTP/HTTPS trackers
	if base.Scheme != "http" && base.Scheme != "https" {
		return nil, 0, fmt.Errorf("unsupported tracker scheme: %s for URL %s", base.Scheme, announceURL)
	}

	params := url.Values{
		"info_hash":  []string{string(tm.InfoHash[:])},
		"peer_id":    []string{string(localPeerID[:])},
		"port":       []string{strconv.Itoa(int(port))},
		"uploaded":   []string{strconv.Itoa(uploaded)},
		"downloaded": []string{strconv.Itoa(downloaded)},
		"left":       []string{strconv.Itoa(left)},
		"compact":    []string{"1"},  // Request compact peer list (binary model)
		"numwant":    []string{"50"}, // Request up to 50 peers
		// "event":      []string{"started"}, // Could be 'started', 'completed', 'stopped', or omitted
	}
	// TODO: Add 'event' based on actual download state
	base.RawQuery = params.Encode()
	reqURL := base.String()

	httpClient := http.Client{Timeout: 10 * time.Second} // Timeout for tracker request
	resp, err := httpClient.Get(reqURL)
	if err != nil {
		return nil, 0, fmt.Errorf("tracker HTTP GET request to %s failed: %w", reqURL, err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		bodyBytes, _ := io.ReadAll(resp.Body)
		return nil, 0, fmt.Errorf("tracker request to %s failed with status %s. Body: %s", reqURL, resp.Status, string(bodyBytes))
	}

	trackerResp := bencodeTrackerResp{}
	err = bencode.Unmarshal(resp.Body, &trackerResp)
	if err != nil {
		return nil, 0, fmt.Errorf("failed to bdecode tracker response from %s: %w", reqURL, err)
	}

	if trackerResp.FailureReason != "" {
		return nil, 0, fmt.Errorf("tracker %s reported failure: %s", reqURL, trackerResp.FailureReason)
	}

	peers, err := UnmarshalPeers([]byte(trackerResp.Peers)) // Ignores Peers6 for now
	if err != nil {
		return nil, 0, fmt.Errorf("failed to unmarshal peers from tracker %s: %w", reqURL, err)
	}

	interval := trackerResp.Interval
	if interval == 0 { // Default interval if not specified
		interval = 1800 // 30 minutes
	}
	if trackerResp.MinInterval > 0 && interval < trackerResp.MinInterval {
		interval = trackerResp.MinInterval
	}

	return peers, interval, nil
}

// requestPeersFromUDPTracker attempts to get peers from a UDP tracker
func (tm *TorrentMetadata) requestPeersFromUDPTracker(
	announceURL string, localPeerID [20]byte, port uint16,
	downloaded, uploaded, left int,
) ([]Peer, int, error) {
	return nil, 0, fmt.Errorf("UDP tracker support has been removed")
}

// --- From p2p.go ---
// MaxBlockSize is the largest number of bytes a request can ask for from a peer
const MaxBlockSize = 16384 // 16 KiB, a common value

// MaxBacklog is the number of unfulfilled piece requests a client can have in its pipeline to one peer
const MaxBacklog = 5

// ActiveTorrent holds data and state for an ongoing torrent download operation
// (Renamed from p2p.Torrent)
type ActiveTorrent struct {
	PeerID       [20]byte // Our client's peer ID for this torrent session
	InfoHash     [20]byte
	PieceHashes  [][20]byte
	PieceLength  int
	TotalLength  int    // Renamed from Length to avoid confusion
	Name         string // Torrent's root name
	Files        []BencodeFile
	IsSingleFile bool
	Meta         *TorrentMetadata // Reference to original metadata (needed for seeding)

	// GUI related bindings & state
	statusBinding         binding.String
	progressBinding       binding.Float  // 0.0 to 1.0
	downloadSpeedBinding  binding.String // Formatted string like "1.2 MB/s"
	uploadSpeedBinding    binding.String // Formatted string (Placeholder)
	peersConnectedBinding binding.Int    // Number of currently connected peers
	etaBinding            binding.String // Estimated time remaining

	dataBuffer            []byte   // Holds the entire downloaded data (all pieces concatenated)
	pieceDownloaded       Bitfield // Our own bitfield indicating verified downloaded pieces
	totalPieces           int
	downloadedPiecesCount int // Count of verified pieces

	mu sync.Mutex // Protects mutable fields like downloadedPiecesCount, dataBuffer, etc.

	ctx        context.Context    // For signalling cancellation/pause to worker goroutines
	cancelFunc context.CancelFunc // Function to call to trigger cancellation

	downloadPath string // Full path to save directory or single file

	// Callbacks for TorrentManager
	onComplete       func()
	onError          func(error)
	onProgressUpdate func() // Generic UI refresh trigger

	// Seeding related fields
	seeder             *seeding.Seeder // Manages the seeding process
	isSeeding          bool            // Whether we're actively seeding
	totalUploadedBytes int64           // Total bytes uploaded while seeding

	// Internal state
	trackerPeers           []Peer                 // Peers obtained from tracker
	connectedPeers         map[string]*PeerClient // key: peer.String()
	workQueue              chan *pieceWork        // Pieces that need to be downloaded
	resultsQueue           chan *pieceResult      // Verified downloaded pieces
	lastTrackerRequestTime time.Time
	trackerInterval        int   // Seconds
	totalDownloadedBytes   int64 // For speed calculation
	// totalUploadedBytes is now a field in the ActiveTorrent struct
}

// pieceWork represents a piece that needs tobe downloaded. Sent to download workers.
type pieceWork struct {
	index  int      // Piece index
	hash   [20]byte // Expected SHA1 hash of the piece
	length int      // Length of this specific piece (can be shorter for the last piece)
}

// pieceResult represents a downloaded (and hash-verified) piece. Sent from workers.
type pieceResult struct {
	index int
	buf   []byte // Raw data of the piece
}

// pieceProgress tracks the download state of a single piece from a single peer.
type pieceProgressState struct {
	index      int
	client     *PeerClient // The peer we are downloading this piece from
	buf        []byte      // Buffer to store incoming blocks for this piece
	downloaded int         // Bytes downloaded for this piece so far
	requested  int         // Bytes requested for this piece so far
	backlog    int         // Number of pending block requests for this piece to this peer
}

// readMessageFromPeer handles incoming messages for a piece download worker.
func (pps *pieceProgressState) readMessageFromPeer() error {
	// This function is called within attemptDownloadPiece, which sets a deadline on the connection.
	// Thus, Read() will eventually time out if the peer is unresponsive.
	if pps.client.Conn == nil {
		return fmt.Errorf("nil connection in readMessageFromPeer")
	}
	msg, err := pps.client.Read()
	if err != nil {
		return err // Could be timeout, connection closed, or other error
	}

	if msg == nil { // Keep-alive
		return nil
	}

	switch msg.ID {
	case MsgUnchoke:
		pps.client.Choked = false
	case MsgChoke:
		pps.client.Choked = true
	case MsgHave:
		index, err := ParseHave(msg)
		if err != nil {
			// log.Printf("Error parsing HAVE message from %s: %v", pps.client.peer.String(), err)
			return err // Potentially recoverable, or peer is misbehaving
		}
		if pps.client.Bitfield != nil {
			pps.client.Bitfield.SetPiece(index)
		}
	case MsgPiece:
		if len(pps.buf) == 0 {
			return fmt.Errorf("piece buffer not initialized for piece index %d", pps.index)
		}
		n, err := ParsePiece(pps.index, pps.buf, msg)
		if err != nil {
			// log.Printf("Error parsing PIECE message for index %d from %s: %v", pps.index, pps.client.peer.String(), err)
			return err
		}
		pps.downloaded += n
		pps.backlog--
	default:
		// log.Printf("Peer %s sent unhandled message ID %d (%s)", pps.client.peer.String(), msg.ID, msg.name())
	}
	return nil
}

// attemptDownloadPiece tries to download a full piece from a single peer.
func attemptDownloadPiece(pCtx context.Context, c *PeerClient, pw *pieceWork) ([]byte, error) {
	state := pieceProgressState{
		index:  pw.index,
		client: c,
		buf:    make([]byte, pw.length), // Buffer for this piece
	}
	if c.Conn == nil {
		return nil, fmt.Errorf("peer client connection is nil for piece %d", pw.index)
	}

	// Set an overall deadline for downloading this piece from this peer.
	// This helps unstick from unresponsive peers for a specific piece.
	// Timeout should be generous enough for a piece but not indefinite.
	// e.g., 30 seconds for a 256KB piece is ~8.5KB/s, quite slow.
	// MaxBlockSize * MaxBacklog could be up to 16KB * 5 = 80KB.
	// If pieceLength is 256KB, it would take 256/16 = 16 requests.
	// If each request/response round trip takes 1-2s, 30-60s seems reasonable for a piece.
	pieceDownloadTimeout := 60 * time.Second
	c.Conn.SetDeadline(time.Now().Add(pieceDownloadTimeout))
	defer c.Conn.SetDeadline(time.Time{}) // Clear deadline after function returns

	for state.downloaded < pw.length {
		select {
		case <-pCtx.Done(): // Check for cancellation (pause/stop torrent)
			return nil, pCtx.Err()
		default:
			// Continue if not cancelled
		}

		if c.Choked { // If peer is choking us, we can't request blocks
			// We need to wait for an Unchoke message.
			// The readMessage loop will handle this by blocking on Read().
			// If choked for too long, the outer deadline will trigger.
			// Optionally, add a specific "choked too long" timeout here.
		} else { // Not choked by peer, so we can send requests
			for state.backlog < MaxBacklog && state.requested < pw.length {
				blockSize := MaxBlockSize
				if pw.length-state.requested < blockSize { // Last block might be shorter
					blockSize = pw.length - state.requested
				}

				err := c.SendRequest(pw.index, state.requested, blockSize)
				if err != nil {
					// log.Printf("Failed to send request for piece %d (offset %d, len %d) to %s: %v", pw.index, state.requested, blockSize, c.peer.String(), err)
					return nil, err
				}
				state.backlog++
				state.requested += blockSize
			}
		}

		// Read messages from the peer (e.g., PIECE, CHOKE, UNCHOKE)
		err := state.readMessageFromPeer()
		if err != nil {
			// This error could be a net.Error (like timeout due to deadline), io.EOF, or parsing error.
			// If it's a timeout, the deadline set earlier likely triggered.
			// log.Printf("Error reading message while downloading piece %d from %s: %v", pw.index, c.peer.String(), err)
			return nil, err
		}
	}

	if state.downloaded != pw.length { // Should not happen if loop terminates correctly
		return nil, fmt.Errorf("piece %d download incomplete: got %d/%d bytes from %s", pw.index, state.downloaded, pw.length, c.peer.String())
	}
	return state.buf, nil
}

// checkPieceIntegrity verifies the SHA1 hash of a downloaded piece.
func checkPieceIntegrity(pw *pieceWork, buf []byte) error {
	if len(buf) != pw.length { // Should not happen if piece is fully downloaded. Paranoia check.
		return fmt.Errorf("integrity check: buffer length %d != piece work length %d for index %d", len(buf), pw.length, pw.index)
	}
	hash := sha1.Sum(buf)
	if !bytes.Equal(hash[:], pw.hash[:]) {
		return fmt.Errorf("piece #%d failed integrity check. Expected %x, got %x", pw.index, pw.hash, hash)
	}
	return nil
}

// downloadWorker is a goroutine that connects to a single peer and downloads pieces.
func (at *ActiveTorrent) downloadWorker(pCtx context.Context, peer Peer) {
	defer func() { // Ensure cleanup on exit
		at.mu.Lock()
		delete(at.connectedPeers, peer.String())
		at.mu.Unlock()
		_ = at.peersConnectedBinding.Set(len(at.connectedPeers)) // Update UI
		// log.Printf("Disconnected from peer %s. Active peers: %d", peer.String(), len(at.connectedPeers))
	}()

	// log.Printf("Attempting to connect to peer %s for torrent %s", peer.String(), at.Name)
	numPiecesInTorrent := len(at.PieceHashes)
	c, err := NewPeerClient(peer, at.PeerID, at.InfoHash, numPiecesInTorrent)
	if err != nil {
		// log.Printf("Failed to establish connection with peer %s: %v", peer.String(), err)
		return // Worker exits if connection fails
	}
	defer c.Conn.Close()
	// log.Printf("Successfully connected to peer %s. Peer's bitfield len: %d bytes.", peer.String(), len(c.Bitfield))

	at.mu.Lock()
	at.connectedPeers[peer.String()] = c
	at.mu.Unlock()
	_ = at.peersConnectedBinding.Set(len(at.connectedPeers)) // Update UI

	// Express interest in downloading from this peer
	if err := c.SendInterested(); err != nil {
		// log.Printf("Failed to send Interested to peer %s: %v", peer.String(), err)
		return
	}

	for {
		select {
		case <-pCtx.Done(): // Torrent is being paused or stopped
			// log.Printf("Download worker for peer %s stopping due to context cancellation.", peer.String())
			return
		case workToDo, ok := <-at.workQueue:
			if !ok { // Work queue has been closed (e.g., all pieces scheduled or torrent stopped)
				// log.Printf("Work queue closed for peer %s.", peer.String())
				return
			}

			// Check if peer has this piece
			if !c.Bitfield.HasPiece(workToDo.index) {
				// Peer doesn't have this piece. Put it back on the queue for another worker.
				// Non-blocking send back or it might deadlock if queue is full and all workers are here.
				select {
				case at.workQueue <- workToDo:
				default: // If queue is full, another worker will pick it up or it's already handled.
				}
				// Consider a small delay or alternative strategy if peers frequently don't have pieces.
				time.Sleep(100 * time.Millisecond)
				continue
			}

			// Peer has the piece, attempt to download it
			// log.Printf("Peer %s attempting to download piece #%d (%s)", peer.String(), workToDo.index, at.Name)
			pieceData, err := attemptDownloadPiece(pCtx, c, workToDo)
			if err != nil {
				// log.Printf("Failed to download piece #%d from peer %s: %v. Re-queuing piece.", workToDo.index, peer.String(), err)
				// Put piece back on queue
				select {
				case at.workQueue <- workToDo:
				default:
				}
				// If error is critical (e.g., repeated timeouts, connection reset), this worker might exit.
				// For now, assume peer might recover or another peer will get it.
				// If context was cancelled, the loop will exit on next iteration.
				if err == context.Canceled || err == context.DeadlineExceeded || err == io.EOF {
					return // Worker exits on critical errors or context done
				}
				continue // Try next piece from queue or wait
			}

			// Piece downloaded, now verify integrity
			err = checkPieceIntegrity(workToDo, pieceData)
			if err != nil {
				log.Printf("Piece #%d from peer %s failed integrity check: %v. Re-queuing.", workToDo.index, peer.String(), err)
				select {
				case at.workQueue <- workToDo:
				default:
				}
				// This peer might be sending corrupt data. Could penalize or disconnect.
				continue
			}

			// Piece is good! Send it to the results queue for assembly.
			at.resultsQueue <- &pieceResult{workToDo.index, pieceData}

			// Tell the peer we now have this piece (if we are acting as a seeder too)
			if err := c.SendHave(workToDo.index); err != nil {
				// log.Printf("Failed to send HAVE for piece #%d to %s: %v", workToDo.index, peer.String(), err)
				// Not fatal for download, but affects peer's knowledge of our state
			}
		}
	}
}

// calculateBoundsForPiece determines the start and end byte offsets for a piece within the total torrent data.
func (at *ActiveTorrent) calculateBoundsForPiece(index int) (begin int, end int) {
	begin = index * at.PieceLength
	end = begin + at.PieceLength
	if end > at.TotalLength {
		end = at.TotalLength
	}
	return begin, end
}

// calculatePieceSize calculates the actual byte size of a specific piece.
func (at *ActiveTorrent) calculatePieceSize(index int) int {
	begin, end := at.calculateBoundsForPiece(index)
	return end - begin
}

// updateGUIGlobals calculates and updates overall progress, speed, and ETA.
func (at *ActiveTorrent) updateGUIGlobals() {
	at.mu.Lock()
	defer at.mu.Unlock()

	if at.totalPieces == 0 {
		_ = at.progressBinding.Set(0)
		return
	}

	progress := float64(at.downloadedPiecesCount) / float64(at.totalPieces)
	_ = at.progressBinding.Set(progress)

	// Speed and ETA calculation would need to track bytes downloaded over time.
	// This is a simplified update. Actual speed calculation happens in downloadLogic's ticker.
	// ETA also requires speed.

	if at.onProgressUpdate != nil {
		at.onProgressUpdate() // Trigger general UI refresh if needed
	}
}

// StartDownload initializes and begins the download process for the torrent.
func (at *ActiveTorrent) StartDownload(downloadDir string, meta *TorrentMetadata) {
	at.mu.Lock()
	// Populate ActiveTorrent fields from TorrentMetadata
	at.InfoHash = meta.InfoHash
	at.PieceHashes = meta.PieceHashes
	at.PieceLength = meta.PieceLength
	at.TotalLength = meta.Length
	at.Name = meta.Name
	at.Files = meta.Files
	at.IsSingleFile = meta.IsSingleFile
	at.Meta = meta // Store reference to original metadata for seeding

	at.totalPieces = len(at.PieceHashes)
	if at.totalPieces == 0 && at.TotalLength > 0 {
		// log.Printf("Error for torrent %s: Has length %d but 0 pieces.", at.Name, at.TotalLength)
		_ = at.statusBinding.Set(StatusError + ": No pieces defined")
		if at.onError != nil {
			at.onError(fmt.Errorf("no pieces defined for torrent with length > 0"))
		}
		at.mu.Unlock()
		return
	}
	if at.totalPieces == 0 && at.TotalLength == 0 { // Empty torrent
		_ = at.statusBinding.Set(StatusCompleted) // Or "Empty"
		_ = at.progressBinding.Set(1.0)
		if at.onComplete != nil {
			at.onComplete()
		}
		at.mu.Unlock()
		return
	}

	// Initialize data structures if this is a fresh start or resume without saved state
	if at.dataBuffer == nil {
		at.dataBuffer = make([]byte, at.TotalLength)
	}
	if at.pieceDownloaded == nil {
		at.pieceDownloaded = make(Bitfield, (at.totalPieces+7)/8)
	}
	// For a real resume, here you would load `pieceDownloaded` and `dataBuffer` from disk
	// and recalculate `downloadedPiecesCount`.

	at.ctx, at.cancelFunc = context.WithCancel(context.Background())
	// Construct full download path
	if at.IsSingleFile {
		at.downloadPath = filepath.Join(downloadDir, at.Name)
	} else {
		at.downloadPath = filepath.Join(downloadDir, at.Name) // This will be the root directory for multi-file
	}

	if at.PeerID == ([20]byte{}) { // Generate our peer ID if not already set (e.g., first run)
		if _, err := rand.Read(at.PeerID[:]); err != nil {
			log.Printf("Error generating peer ID for %s: %v", at.Name, err)
			_ = at.statusBinding.Set(StatusError + ": " + err.Error())
			if at.onError != nil {
				at.onError(err)
			}
			at.mu.Unlock()
			return
		}
	}
	at.connectedPeers = make(map[string]*PeerClient)
	at.workQueue = make(chan *pieceWork, at.totalPieces) // Buffered queue for all pieces
	at.resultsQueue = make(chan *pieceResult)            // Unbuffered, process one by one

	at.mu.Unlock() // Unlock before starting goroutine

	log.Printf("Starting download process for: %s (Total size: %s, Pieces: %d)", at.Name, formatSize(at.TotalLength), at.totalPieces)
	_ = at.statusBinding.Set(StatusConnectingTrackers)
	at.updateGUIGlobals()

	go at.downloadLogic(meta) // Pass meta for tracker URLs
}

// StopDownload signals the download goroutines to stop (acts as pause).
func (at *ActiveTorrent) StopDownload() {
	at.mu.Lock()
	if at.cancelFunc != nil {
		at.cancelFunc()     // Signal cancellation to context
		at.cancelFunc = nil // Prevent multiple calls
	}

	// Stop seeding if active
	if at.isSeeding && at.seeder != nil {
		at.seeder.Stop()
		at.isSeeding = false
	}

	// Current goroutines will clean up. If resuming, new ones are made.
	_ = at.statusBinding.Set(StatusPaused)
	_ = at.downloadSpeedBinding.Set(formatSpeed(0)) // Reset speed on pause
	_ = at.uploadSpeedBinding.Set(formatSpeed(0))   // Reset upload speed on pause
	_ = at.etaBinding.Set("-")
	at.mu.Unlock()
	log.Printf("Download/seeding paused for %s", at.Name)
}

// ResumeDownload restarts the download process for a paused torrent.
func (at *ActiveTorrent) ResumeDownload(downloadDir string, meta *TorrentMetadata) {
	currentStatus, _ := at.statusBinding.Get()

	// Check if download is already running
	if currentStatus == StatusDownloading {
		return // Already downloading
	}

	// Check if the torrent is completed but not seeding
	if currentStatus == StatusCompleted {
		// If completed but not seeding, start seeding
		if !at.isSeeding {
			log.Printf("Torrent %s is completed, starting seeding", at.Name)
			at.startSeeding()
			return
		}
		return // Already completed and seeding
	}

	// If already seeding, resume seeding
	if currentStatus == StatusSeeding && !at.isSeeding {
		log.Printf("Resuming seeding for %s", at.Name)
		at.startSeeding()
		return
	}

	log.Printf("Resuming download for %s", at.Name)
	// State (like downloaded pieces, dataBuffer) is preserved in ActiveTorrent instance.
	// StartDownload will re-initialize context, queues, and launch downloadLogic.
	at.StartDownload(downloadDir, meta) // Re-use StartDownload which sets up everything
}

// downloadLogic is the main goroutine orchestrating the download.
func (at *ActiveTorrent) downloadLogic(meta *TorrentMetadata) {
	defer func() { // Ensure status is updated on exit from this goroutine
		at.mu.Lock()
		// If not completed or intentionally paused/stopped, mark as stalled or error
		currentStatus, _ := at.statusBinding.Get()
		if currentStatus != StatusCompleted && currentStatus != StatusPaused && currentStatus != StatusStopped && !strings.HasPrefix(currentStatus, StatusError) {
			if at.totalPieces > 0 && at.downloadedPiecesCount < at.totalPieces {
				_ = at.statusBinding.Set(StatusStalled + " (Interrupted)")
			} else if at.totalPieces > 0 && at.downloadedPiecesCount == at.totalPieces {
				_ = at.statusBinding.Set(StatusCompleted) // Should have been set by main loop if completed
			}
		}
		// Clean up connected peers map if workers didn't all exit cleanly before this defer runs
		for _, client := range at.connectedPeers {
			if client.Conn != nil {
				client.Conn.Close()
			}
		}
		at.connectedPeers = make(map[string]*PeerClient) // Clear map
		_ = at.peersConnectedBinding.Set(0)
		_ = at.downloadSpeedBinding.Set(formatSpeed(0))
		_ = at.etaBinding.Set("-")
		at.mu.Unlock()
	}()

	// --- Phase 1: Get Peers from Tracker ---
	at.mu.Lock()
	initialPeers, interval, err := meta.GetPeers(at.PeerID, OurClientPort, int(at.totalDownloadedBytes), int(at.totalUploadedBytes), at.TotalLength-int(at.totalDownloadedBytes))
	at.lastTrackerRequestTime = time.Now()
	at.trackerInterval = interval
	if err != nil {
		log.Printf("Error getting peers for %s: %v", at.Name, err)
		_ = at.statusBinding.Set(StatusError + ": Tracker issue")
		if at.onError != nil {
			at.onError(err)
		}
		at.mu.Unlock()
		return
	}
	at.trackerPeers = initialPeers
	if len(at.trackerPeers) == 0 {
		log.Printf("No peers found from trackers for %s.", at.Name)
		_ = at.statusBinding.Set(StatusStalled + " (No Peers from Tracker)")
		// Don't call onError, this is a common state. Torrent might pick up later.
		at.mu.Unlock()
		return // Can't proceed without peers
	}
	at.mu.Unlock()
	_ = at.statusBinding.Set(StatusDownloading)

	// --- Phase 2: Populate Work Queue ---
	at.mu.Lock()
	pendingPiecesCount := 0
	for i := 0; i < at.totalPieces; i++ {
		if !at.pieceDownloaded.HasPiece(i) {
			pieceLen := at.calculatePieceSize(i)
			at.workQueue <- &pieceWork{index: i, hash: at.PieceHashes[i], length: pieceLen}
			pendingPiecesCount++
		}
	}
	at.mu.Unlock()

	if pendingPiecesCount == 0 { // All pieces already downloaded (e.g. on resume with fully downloaded file)
		log.Printf("All pieces for %s are already marked as downloaded.", at.Name)
		close(at.workQueue) // No work needed
		_ = at.statusBinding.Set(StatusCompleted)
		at.finalizeAndSave()
		if at.onComplete != nil {
			at.onComplete()
		}
		return
	}

	// --- Phase 3: Start Download Workers for initial set of peers ---
	maxConcurrentPeers := 50 // Configurable: how many peers to connect to simultaneously
	peersToConnect := at.trackerPeers
	if len(peersToConnect) > maxConcurrentPeers {
		peersToConnect = peersToConnect[:maxConcurrentPeers] // Limit initial connections
	}
	for _, peer := range peersToConnect {
		go at.downloadWorker(at.ctx, peer)
	}

	// --- Phase 4: Main Download Loop (Process results, manage workers, update UI) ---
	ticker := time.NewTicker(1 * time.Second) // For periodic updates (speed, ETA, tracker)
	defer ticker.Stop()

	var bytesDownloadedThisInterval int64

	for at.downloadedPiecesCount < at.totalPieces {
		select {
		case <-at.ctx.Done(): // Torrent paused or stopped
			log.Printf("Download logic for %s stopping due to context cancellation.", at.Name)
			// Status will be set by StopDownload() or similar external call.
			return

		case pieceRes := <-at.resultsQueue:
			at.mu.Lock()
			if !at.pieceDownloaded.HasPiece(pieceRes.index) { // Ensure not already processed
				begin, end := at.calculateBoundsForPiece(pieceRes.index)
				copy(at.dataBuffer[begin:end], pieceRes.buf)
				at.pieceDownloaded.SetPiece(pieceRes.index)
				at.downloadedPiecesCount++

				// Update total downloaded bytes for speed calculation
				chunkSize := int64(len(pieceRes.buf))
				at.totalDownloadedBytes += chunkSize
				bytesDownloadedThisInterval += chunkSize
				// log.Printf("Verified and stored piece #%d for %s. Total downloaded: %d/%d", pieceRes.index, at.Name, at.downloadedPiecesCount, at.totalPieces)
			}
			at.mu.Unlock()
			at.updateGUIGlobals() // Update progress bar and other piece-count dependent UI

		case <-ticker.C:
			// Calculate download speed
			currentSpeed := float64(bytesDownloadedThisInterval) // bytes/sec
			_ = at.downloadSpeedBinding.Set(formatSpeed(currentSpeed))
			bytesDownloadedThisInterval = 0 // Reset for next interval

			// Calculate ETA
			if currentSpeed > 0 {
				at.mu.Lock()
				remainingBytes := at.TotalLength - int(at.totalDownloadedBytes)
				at.mu.Unlock()
				if remainingBytes > 0 {
					etaSeconds := float64(remainingBytes) / currentSpeed
					_ = at.etaBinding.Set(time.Duration(etaSeconds * float64(time.Second)).Round(time.Second).String())
				} else {
					_ = at.etaBinding.Set("Done")
				}
			} else if at.downloadedPiecesCount < at.totalPieces {
				_ = at.etaBinding.Set("âˆž") // Infinite if no speed and not done
			}

			// Manage peer connections: connect to more if needed, less than maxConcurrentPeers
			at.mu.Lock()
			numConnected := len(at.connectedPeers)
			// Potentially refresh peer list from tracker if interval has passed
			if time.Since(at.lastTrackerRequestTime).Seconds() > float64(at.trackerInterval) && numConnected < maxConcurrentPeers/2 {
				// log.Printf("Requesting more peers from tracker for %s", at.Name)
				// This tracker request should ideally be in its own goroutine to not block this loop
				// For simplicity, it's currently synchronous.
				newPeers, newInterval, tErr := meta.GetPeers(at.PeerID, OurClientPort, int(at.totalDownloadedBytes), int(at.totalUploadedBytes), at.TotalLength-int(at.totalDownloadedBytes))
				at.lastTrackerRequestTime = time.Now()
				if tErr == nil {
					at.trackerInterval = newInterval
					// Add new unique peers to at.trackerPeers and potentially start workers for them
					existingTrackedPeers := make(map[string]struct{})
					for _, p := range at.trackerPeers {
						existingTrackedPeers[p.String()] = struct{}{}
					}

					// Variable to track if any new peers were found
					for _, np := range newPeers {
						if _, exists := existingTrackedPeers[np.String()]; !exists {
							at.trackerPeers = append(at.trackerPeers, np) // Add to general list
							if numConnected < maxConcurrentPeers {        // If we have capacity
								if _, alreadyConnected := at.connectedPeers[np.String()]; !alreadyConnected {
									go at.downloadWorker(at.ctx, np) // Connect to new peer
									numConnected++
									// New peer found and connected
								}
							}
						}
					}
					// log.Printf("Added new peers from tracker for %s", at.Name)
				} else {
					// log.Printf("Failed to get updated peer list from tracker for %s: %v", at.Name, tErr)
				}
			}
			at.mu.Unlock()

			// If no connected peers but download not complete, change status
			if numConnected == 0 && at.downloadedPiecesCount < at.totalPieces {
				currentStatus, _ := at.statusBinding.Get()
				if currentStatus == StatusDownloading { // Only change if it was actively downloading
					_ = at.statusBinding.Set(StatusStalled + " (No active peers)")
				}
			} else if numConnected > 0 && at.downloadedPiecesCount < at.totalPieces {
				currentStatus, _ := at.statusBinding.Get()
				if strings.HasPrefix(currentStatus, StatusStalled) { // If it was stalled, but now has peers
					_ = at.statusBinding.Set(StatusDownloading)
				}
			}
		}
	}

	// --- Phase 5: Download Completion ---
	if at.downloadedPiecesCount == at.totalPieces {
		log.Printf("Download fully completed for %s.", at.Name)
		_ = at.statusBinding.Set(StatusCompleted)
		_ = at.downloadSpeedBinding.Set(formatSpeed(0))
		_ = at.etaBinding.Set("Done")
		at.updateGUIGlobals() // Final progress update to 100%

		if err := at.finalizeAndSave(); err != nil {
			log.Printf("Error finalizing and saving download for %s: %v", at.Name, err)
			_ = at.statusBinding.Set(StatusError + ": Save failed")
			if at.onError != nil {
				at.onError(err)
			}
			return
		}
		log.Printf("Successfully saved %s to %s", at.Name, at.downloadPath)

		// Start seeding now that download is complete
		at.startSeeding()

		if at.onComplete != nil {
			at.onComplete()
		}
	} else {
		// This path should ideally not be reached if context cancellation is handled.
		// If loop exited for other reasons while incomplete.
		if at.ctx.Err() == nil { // If not due to explicit cancellation
			log.Printf("Download loop for %s exited prematurely. Downloaded %d/%d pieces.", at.Name, at.downloadedPiecesCount, at.totalPieces)
			_ = at.statusBinding.Set(StatusStalled + " (Incomplete)")
		}
	}
}

// startSeeding begins the seeding process for a completed torrent
func (at *ActiveTorrent) startSeeding() {
	at.mu.Lock()
	defer at.mu.Unlock()

	if at.isSeeding {
		return
	}

	// Create seeder if it doesn't exist
	if at.seeder == nil {
		var err error
		at.seeder, err = seeding.NewSeeder(at.Meta.Announce, OurClientPort)
		if err != nil {
			log.Printf("Failed to create seeder: %v", err)
			return
		}

		// Convert files to seeding.BencodeFile type
		seedingFiles := make([]seeding.BencodeFile, len(at.Files))
		for i, file := range at.Files {
			seedingFiles[i] = seeding.BencodeFile{
				Length: int64(file.Length),
				Path:   file.Path,
			}
		}

		// Set torrent info
		at.seeder.SetTorrentInfo(
			at.InfoHash,
			at.PieceLength,
			at.totalPieces,
			int64(at.TotalLength),
			at.Name,
			at.IsSingleFile,
			seedingFiles,
		)

		// Set file paths
		var filePaths []string
		if at.IsSingleFile {
			filePaths = []string{at.downloadPath}
		} else {
			// For multi-file torrents, collect all file paths
			for _, file := range at.Files {
				pathParts := append([]string{at.downloadPath}, file.Path...)
				filePaths = append(filePaths, filepath.Join(pathParts...))
			}
		}
		at.seeder.SetFilePaths(filePaths)

		// Start seeding
		if err := at.seeder.Start(); err != nil {
			log.Printf("Failed to start seeding: %v", err)
			at.seeder = nil
			return
		}
	}

	at.isSeeding = true
	_ = at.statusBinding.Set(StatusSeeding)
	log.Printf("Started seeding for %s on port %d", at.Name, OurClientPort)
}

// StopSeeding stops the seeding process
func (at *ActiveTorrent) StopSeeding() {
	at.mu.Lock()
	defer at.mu.Unlock()

	if at.seeder != nil && at.isSeeding {
		at.seeder.Stop()
		at.isSeeding = false
		_ = at.statusBinding.Set(StatusCompleted)     // Revert to completed status
		_ = at.uploadSpeedBinding.Set(formatSpeed(0)) // Reset upload speed display
		log.Printf("Stopped seeding for %s", at.Name)
	}
}

// IsSeeding returns whether the torrent is currently seeding
func (at *ActiveTorrent) IsSeeding() bool {
	at.mu.Lock()
	defer at.mu.Unlock()
	return at.isSeeding
}

// finalizeAndSave writes the completed torrent data (from dataBuffer) to disk.
func (at *ActiveTorrent) finalizeAndSave() error {
	at.mu.Lock() // Lock to protect dataBuffer and file paths
	defer at.mu.Unlock()

	log.Printf("Finalizing download for %s. Saving to directory/file: %s.", at.Name, at.downloadPath)

	// Create base directory for multi-file torrent or directory for single file if needed.
	// For single file, at.downloadPath is the file itself. Its Dir is the target.
	// For multi-file, at.downloadPath is the root directory for the torrent.
	var targetDir string
	if at.IsSingleFile {
		targetDir = filepath.Dir(at.downloadPath)
	} else {
		targetDir = at.downloadPath // This is already <downloadDir>/<TorrentName>
	}
	if err := os.MkdirAll(targetDir, 0755); err != nil {
		return fmt.Errorf("could not create target directory %s: %w", targetDir, err)
	}

	fileOffset := 0
	for _, fileInfo := range at.Files {
		var fullPath string
		if at.IsSingleFile {
			fullPath = at.downloadPath // This is already <downloadDir>/<TorrentName.file>
		} else {
			// For multi-file, path components are relative to at.downloadPath (which is <downloadDir>/<TorrentName>)
			pathParts := append([]string{at.downloadPath}, fileInfo.Path...)
			fullPath = filepath.Join(pathParts...)

			// Ensure subdirectory for this file exists
			if err := os.MkdirAll(filepath.Dir(fullPath), 0755); err != nil {
				return fmt.Errorf("could not create subdirectory %s for file %s: %w", filepath.Dir(fullPath), filepath.Base(fullPath), err)
			}
		}

		outFile, err := os.Create(fullPath)
		if err != nil {
			return fmt.Errorf("could not create file %s: %w", fullPath, err)
		}

		if fileOffset+fileInfo.Length > len(at.dataBuffer) {
			outFile.Close()
			return fmt.Errorf("data buffer (%d bytes) too small for file %s (offset %d, length %d)",
				len(at.dataBuffer), fullPath, fileOffset, fileInfo.Length)
		}

		_, err = outFile.Write(at.dataBuffer[fileOffset : fileOffset+fileInfo.Length])
		if err != nil {
			outFile.Close()
			return fmt.Errorf("could not write to file %s: %w", fullPath, err)
		}
		outFile.Close() // Close after successful write
		fileOffset += fileInfo.Length
	}
	return nil
}

// --- Global App State & GUI Elements ---

// TorrentStatus constants for UI display consistency
const (
	StatusConnectingTrackers = "Connecting to trackers..."
	StatusDownloading        = "Downloading"
	StatusPaused             = "Paused"
	StatusStopped            = "Stopped"
	StatusCompleted          = "Completed"
	StatusSeeding            = "Seeding"
	StatusStalled            = "Stalled"
	StatusError              = "Error"
	StatusCheckingFiles      = "Checking files..."
	StatusQueued             = "Queued"
)

// ManagedTorrent wraps ActiveTorrent with its original TorrentMetadata and GUI related ID.
type ManagedTorrent struct {
	ID              string           // Unique ID, typically InfoHash hex string
	Meta            *TorrentMetadata // Parsed .torrent file metadata
	Active          *ActiveTorrent   // The active download session state and logic
	TorrentFilePath string           // Path to the original .torrent file for reference
}

// TorrentManager handles the collection of torrents and orchestrates UI updates.
type TorrentManager struct {
	torrents           map[string]*ManagedTorrent // Keyed by InfoHash hex
	torrentListBinding binding.UntypedList        // Data source for the Fyne List widget
	downloadDirectory  string
	fyneApp            fyne.App
	mainWindow         fyne.Window
	mu                 sync.Mutex // Protects torrents map and torrentListBinding operations
}

var globalTorrentManager *TorrentManager // Global instance

// NewTorrentManager creates and initializes a TorrentManager.
func NewTorrentManager(app fyne.App, window fyne.Window, downloadDir string) *TorrentManager {
	return &TorrentManager{
		torrents:           make(map[string]*ManagedTorrent),
		torrentListBinding: binding.NewUntypedList(),
		downloadDirectory:  downloadDir,
		fyneApp:            app,
		mainWindow:         window,
	}
}

// formatSize converts byte count to human-readable string (e.g., "1.2 MiB").
func formatSize(bytes int) string {
	const unit = 1024
	if bytes < unit {
		return fmt.Sprintf("%d B", bytes)
	}
	div, exp := int64(unit), 0
	for n := int64(bytes) / unit; n >= unit; n /= unit {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.1f %ciB", float64(bytes)/float64(div), "KMGTPE"[exp])
}

// formatSpeed converts bytes/second to human-readable string (e.g., "150.5 KiB/s").
func formatSpeed(bytesPerSecond float64) string {
	if bytesPerSecond < 1024 {
		return fmt.Sprintf("%.1f B/s", bytesPerSecond)
	} else if bytesPerSecond < 1024*1024 {
		return fmt.Sprintf("%.1f KiB/s", bytesPerSecond/1024.0)
	} else if bytesPerSecond < 1024*1024*1024 {
		return fmt.Sprintf("%.1f MiB/s", bytesPerSecond/(1024.0*1024.0))
	} else {
		return fmt.Sprintf("%.1f GiB/s", bytesPerSecond/(1024.0*1024.0*1024.0))
	}
}

// AddTorrentFile parses a .torrent file, creates a ManagedTorrent, and starts its download.
func (tm *TorrentManager) AddTorrentFile(filePath string) {
	meta, err := OpenTorrentFile(filePath)
	if err != nil {
		dialog.ShowError(fmt.Errorf("error opening torrent file: %w", err), tm.mainWindow)
		return
	}

	infoHashHex := fmt.Sprintf("%x", meta.InfoHash)

	tm.mu.Lock()
	if _, exists := tm.torrents[infoHashHex]; exists {
		tm.mu.Unlock()
		dialog.ShowInformation("Torrent Exists", "This torrent is already in the list.", tm.mainWindow)
		return
	}

	// Create the ActiveTorrent instance which holds live download state
	active := &ActiveTorrent{
		// PeerID will be generated by ActiveTorrent.StartDownload if needed
		// Other fields (InfoHash, PieceHashes, etc.) will be populated from meta in StartDownload
		statusBinding:         binding.NewString(),
		progressBinding:       binding.NewFloat(),
		downloadSpeedBinding:  binding.NewString(),
		uploadSpeedBinding:    binding.NewString(), // Placeholder
		peersConnectedBinding: binding.NewInt(),
		etaBinding:            binding.NewString(),
	}
	_ = active.statusBinding.Set(StatusQueued) // Initial status
	_ = active.downloadSpeedBinding.Set(formatSpeed(0))
	_ = active.uploadSpeedBinding.Set(formatSpeed(0)) // Placeholder
	_ = active.etaBinding.Set("-")

	mt := &ManagedTorrent{
		ID:              infoHashHex,
		Meta:            meta,
		Active:          active,
		TorrentFilePath: filePath,
	}

	// Setup callbacks from ActiveTorrent back to TorrentManager or UI
	mt.Active.onComplete = func() {
		// log.Printf("Torrent %s download completed callback in TorrentManager.", mt.Meta.Name)
		// Could trigger notifications or change status to Seeding
	}
	mt.Active.onError = func(err error) {
		log.Printf("Torrent %s error callback in TorrentManager: %v", mt.Meta.Name, err)
		// Error status is usually set by ActiveTorrent itself, this could show a dialog
		// dialog.ShowError(fmt.Errorf("download error for %s: %w", mt.Meta.Name, err), tm.mainWindow)
	}
	mt.Active.onProgressUpdate = func() {
		// Fyne's data binding should handle individual field updates.
		// If the entire list item needs a redraw not covered by binding, use:
		// tm.torrentListBinding.Reload() // Be cautious, can be expensive
	}

	tm.torrents[infoHashHex] = mt
	tm.mu.Unlock() // Unlock before appending to list binding if it triggers UI updates

	// Append to UI list. Fyne data binding should handle UI thread safety.
	err = tm.torrentListBinding.Append(mt)
	if err != nil {
		log.Printf("Error appending torrent to UI list: %v", err)
		// Might need to remove from tm.torrents map if append fails critically
		tm.mu.Lock()
		delete(tm.torrents, infoHashHex)
		tm.mu.Unlock()
		dialog.ShowError(fmt.Errorf("failed to add torrent to UI: %w", err), tm.mainWindow)
		return
	}

	// Automatically start the download
	mt.Active.StartDownload(tm.downloadDirectory, mt.Meta)
}

// --- Main GUI Setup ---
var currentSelectedTorrentID string                        // Stores InfoHashHex of the selected torrent in the list
var torrentListWidget *widget.List                         // Reference to the list widget itself
var pauseButton, resumeButton, removeButton *widget.Button // Toolbar buttons for context actions

// main function sets up and runs the Fyne GUI application.
func main() {
	myApp := app.NewWithID("com.go.bittorrentgui") // Unique ID for preferences
	myApp.Settings().SetTheme(theme.DarkTheme())   // Or theme.LightTheme()
	mainWin := myApp.NewWindow("Go Torrent Client GUI")
	mainWin.Resize(fyne.NewSize(900, 700)) // Adjusted size

	// Setup download directory (user's Downloads/GoTorrentClientGUI)
	homeDir, _ := os.UserHomeDir()
	downloadDir := filepath.Join(homeDir, "Downloads", "GoTorrentClientGUI")
	if err := os.MkdirAll(downloadDir, 0755); err != nil {
		log.Fatalf("FATAL: Failed to create download directory %s: %v", downloadDir, err)
	}
	log.Printf("Downloads will be saved to: %s", downloadDir)

	globalTorrentManager = NewTorrentManager(myApp, mainWin, downloadDir)

	// --- Toolbar Setup ---
	addTorrentAction := widget.NewToolbarAction(theme.ContentAddIcon(), func() {
		fileOpenDialog := dialog.NewFileOpen(func(reader fyne.URIReadCloser, err error) {
			if err != nil {
				dialog.ShowError(err, mainWin)
				return
			}
			if reader == nil { // User cancelled dialog
				return
			}
			filePath := reader.URI().Path()
			reader.Close() // Close the reader
			if filePath != "" {
				globalTorrentManager.AddTorrentFile(filePath)
			}
		}, mainWin)
		fileOpenDialog.SetFilter(storage.NewExtensionFileFilter([]string{".torrent"}))
		fileOpenDialog.Show()
	})

	createTorrentAction := widget.NewToolbarAction(theme.DocumentCreateIcon(), func() {
		showCreateTorrentDialog(mainWin, downloadDir) // downloadDir as default save location for .torrent files
	})

	toolbar := widget.NewToolbar(addTorrentAction, widget.NewToolbarSeparator(), createTorrentAction)

	// Contextual action buttons (Pause, Resume, Remove)
	pauseButton = widget.NewButtonWithIcon("Pause", theme.MediaPauseIcon(), func() {
		if currentSelectedTorrentID == "" {
			return
		}
		globalTorrentManager.mu.Lock()
		defer globalTorrentManager.mu.Unlock()
		if mt, ok := globalTorrentManager.torrents[currentSelectedTorrentID]; ok {
			mt.Active.StopDownload()     // StopDownload implements pause
			updateActionButtonsState(mt) // Refresh button states after action
		}
	})
	resumeButton = widget.NewButtonWithIcon("Resume", theme.MediaPlayIcon(), func() {
		if currentSelectedTorrentID == "" {
			return
		}
		globalTorrentManager.mu.Lock()
		defer globalTorrentManager.mu.Unlock()
		if mt, ok := globalTorrentManager.torrents[currentSelectedTorrentID]; ok {
			// Pass meta again for resume, as StartDownload needs it
			mt.Active.ResumeDownload(globalTorrentManager.downloadDirectory, mt.Meta)
			updateActionButtonsState(mt)
		}
	})
	removeButton = widget.NewButtonWithIcon("Remove", theme.DeleteIcon(), func() {
		if currentSelectedTorrentID == "" {
			return
		}

		mt, ok := globalTorrentManager.torrents[currentSelectedTorrentID]
		if !ok {
			return
		}

		dialog.ShowConfirm("Remove Torrent", fmt.Sprintf("Are you sure you want to remove '%s'?\n(Downloaded files will NOT be deleted.)", mt.Meta.Name),
			func(confirm bool) {
				if !confirm {
					return
				}

				globalTorrentManager.mu.Lock()
				torrentToRemove, exists := globalTorrentManager.torrents[currentSelectedTorrentID]
				if !exists {
					globalTorrentManager.mu.Unlock()
					return
				}

				// Stop the download routines first
				if torrentToRemove.Active.cancelFunc != nil {
					torrentToRemove.Active.StopDownload()
				}
				delete(globalTorrentManager.torrents, currentSelectedTorrentID)
				globalTorrentManager.mu.Unlock() // Unlock before modifying UI list

				// Remove from UI list
				listLen := globalTorrentManager.torrentListBinding.Length()
				removedIndex := -1
				for i := 0; i < listLen; i++ {
					item, _ := globalTorrentManager.torrentListBinding.GetValue(i)
					if uiMt, isManaged := item.(*ManagedTorrent); isManaged && uiMt.ID == currentSelectedTorrentID {
						removedIndex = i
						break
					}
				}
				if removedIndex != -1 {
					// Create a new list without the removed item
					// This is safer than trying to modify bound list directly with unsupported RemoveAt type operations
					newList := make([]interface{}, 0, listLen-1)
					for i := 0; i < listLen; i++ {
						if i == removedIndex {
							continue
						}
						val, _ := globalTorrentManager.torrentListBinding.GetValue(i)
						newList = append(newList, val)
					}
					globalTorrentManager.torrentListBinding.Set(newList)
				}

				currentSelectedTorrentID = ""   // Clear selection
				torrentListWidget.UnselectAll() // Visually clear Fyne list selection
				updateActionButtonsState(nil)   // Disable buttons
			}, mainWin)
	})

	// Initially disable context buttons
	updateActionButtonsState(nil)

	actionButtonBox := container.NewHBox(pauseButton, resumeButton, removeButton)
	fullToolbarContainer := container.NewBorder(nil, nil, toolbar, actionButtonBox) // Toolbar on left, actions on right

	// --- Torrent List Widget Setup ---
	torrentListWidget = widget.NewListWithData(
		globalTorrentManager.torrentListBinding,
		// CreateItem: How each item in the list should look initially
		func() fyne.CanvasObject {
			nameLabel := widget.NewLabel("Torrent Name")
			// Remove truncation setting as it's causing type mismatch
			// fyne.TextTruncate is of type fyne.TextWrap but nameLabel.Truncation expects fyne.TextTruncation
			progressBar := widget.NewProgressBar()
			statusLabel := widget.NewLabel("Status")
			sizeLabel := widget.NewLabel("Size: ???")  // Default text
			speedLabel := widget.NewLabel("DL: 0 B/s") // Default text
			peersLabel := widget.NewLabel("Peers: 0")  // Default text
			etaLabel := widget.NewLabel("ETA: -")      // Default text

			// Layout for details (status, size, speed, peers, ETA)
			detailsGrid := container.NewGridWithColumns(5, statusLabel, sizeLabel, speedLabel, peersLabel, etaLabel)

			return container.NewVBox(nameLabel, progressBar, detailsGrid, widget.NewSeparator())
		},
		// UpdateItem: How to update an item's content when its data changes
		func(item binding.DataItem, obj fyne.CanvasObject) {
			managedTorrentUntyped, err := item.(binding.Untyped).Get()
			if err != nil {
				return
			}
			mt, ok := managedTorrentUntyped.(*ManagedTorrent)
			if !ok || mt.Meta == nil || mt.Active == nil {
				return
			} // Safety checks

			boxContainer := obj.(*fyne.Container)
			nameLabel := boxContainer.Objects[0].(*widget.Label)
			progressBar := boxContainer.Objects[1].(*widget.ProgressBar)
			detailsGrid := boxContainer.Objects[2].(*fyne.Container)

			statusLabel := detailsGrid.Objects[0].(*widget.Label)
			sizeLabel := detailsGrid.Objects[1].(*widget.Label)
			speedLabel := detailsGrid.Objects[2].(*widget.Label)
			peersLabel := detailsGrid.Objects[3].(*widget.Label)
			etaLabel := detailsGrid.Objects[4].(*widget.Label)

			nameLabel.SetText(mt.Meta.Name)               // Static text based on metadata
			sizeLabel.SetText(formatSize(mt.Meta.Length)) // Static text

			// Bind dynamic data
			progressBar.Bind(mt.Active.progressBinding)
			statusLabel.Bind(mt.Active.statusBinding)
			speedLabel.Bind(mt.Active.downloadSpeedBinding) // This already includes "DL: "
			peersLabel.Bind(binding.IntToStringWithFormat(mt.Active.peersConnectedBinding, "Peers: %d"))
			etaLabel.Bind(binding.StringToStringWithFormat(mt.Active.etaBinding, "ETA: %s"))
		},
	)

	torrentListWidget.OnSelected = func(id widget.ListItemID) {
		itemUntyped, _ := globalTorrentManager.torrentListBinding.GetValue(id)
		if mt, ok := itemUntyped.(*ManagedTorrent); ok {
			currentSelectedTorrentID = mt.ID
			updateActionButtonsState(mt)
		}
	}
	torrentListWidget.OnUnselected = func(id widget.ListItemID) {
		// This callback seems to trigger also when selection changes, check if a new item is selected.
		// A truly unselected state might need more complex tracking if List doesn't clear selection easily.
		// For now, if list widget itself doesn't have a selected index, then it's unselected.
		// This typically means currentSelectedTorrentID might not be cleared reliably here alone.
		// Let's assume a click outside items or removing the selected item unselects.
		// currentSelectedTorrentID = "" // Potentially problematic if OnSelected fires immediately after for new item
		// updateActionButtonsState(nil)
	}

	// --- Main Window Content ---
	content := container.NewBorder(fullToolbarContainer, nil, nil, nil, torrentListWidget)
	mainWin.SetContent(content)
	mainWin.SetMaster() // Important for dialogs to parent correctly

	// Handle app exit gracefully
	mainWin.SetOnClosed(func() {
		log.Println("Closing application. Stopping all torrents...")
		globalTorrentManager.mu.Lock()
		for _, mt := range globalTorrentManager.torrents {
			if mt.Active.cancelFunc != nil {
				mt.Active.StopDownload() // This calls cancelFunc
			}
		}
		globalTorrentManager.mu.Unlock()
		// Give a moment for goroutines to try to clean up.
		time.Sleep(500 * time.Millisecond)
		log.Println("Exiting.")
	})

	mainWin.ShowAndRun()
}

// updateActionButtonsState enables/disables Pause, Resume, Remove based on selected torrent's state
func updateActionButtonsState(mt *ManagedTorrent) {
	if mt == nil || mt.Active == nil { // No selection or invalid torrent
		pauseButton.Disable()
		resumeButton.Disable()
		removeButton.Disable()
		return
	}

	status, _ := mt.Active.statusBinding.Get()
	removeButton.Enable() // Always possible to remove a selected torrent

	switch status {
	case StatusDownloading:
		pauseButton.Enable()
		resumeButton.Disable()
	case StatusPaused, StatusStopped, StatusError, StatusStalled, StatusQueued, StatusConnectingTrackers:
		pauseButton.Disable()
		resumeButton.Enable()
	case StatusCompleted:
		// For completed torrents, enable resume to start seeding
		pauseButton.Disable()
		resumeButton.Enable()
	case StatusSeeding:
		// For seeding torrents, enable pause to stop seeding
		pauseButton.Enable()
		resumeButton.Disable()
	default: // Unknown status
		pauseButton.Disable()
		resumeButton.Disable()
	}
}

// --- Create Torrent Functionality ---
func showCreateTorrentDialog(win fyne.Window, defaultSaveDir string) {
	var sourceItem fyne.URI       // Can be file or folder
	torrentName := "MyNewTorrent" // Default
	pieceSize := 256 * 1024       // Default 256KB
	// Tracker URLs will be collected from the announceEntry field

	sourceEntry := widget.NewEntry()
	sourceEntry.SetPlaceHolder("Path to file or directory")
	sourceEntry.Disable() // User must use Browse

	torrentNameEntry := widget.NewEntry()
	torrentNameEntry.SetText(torrentName)

	pieceSizeOptions := []string{
		"32 KiB", "64 KiB", "128 KiB", "256 KiB", "512 KiB", "1 MiB", "2 MiB", "4 MiB", "8 MiB", "16 MiB",
	}
	pieceSizeSelect := widget.NewSelect(pieceSizeOptions, func(s string) {
		val, unit := 0, ""
		fmt.Sscanf(s, "%d %s", &val, &unit)
		multiplier := 1024 // KiB
		if unit == "MiB" {
			multiplier = 1024 * 1024
		}
		pieceSize = val * multiplier
	})
	pieceSizeSelect.SetSelected("256 KiB") // Default selection matching pieceSize var

	announceEntry := widget.NewMultiLineEntry()
	announceEntry.SetPlaceHolder("Tracker URLs (one per line or comma-separated)")
	announceEntry.SetMinRowsVisible(3)
	// Could prefill with common public trackers if desired

	browseButton := widget.NewButton("Browse Source...", func() {
		// We need a dialog that can select either a file or a folder.
		// Fyne's standard dialogs are ShowFileOpen or ShowFolderOpen.
		// We can offer two buttons, or a radio choice for file/folder.
		// For simplicity, let's use ShowFolderOpen, assuming users torrent directories often.
		// Or ShowFileOpen for a single file.
		// Let's allow both via a generic Open dialog.
		openDialog := dialog.NewFileOpen(func(readCloser fyne.URIReadCloser, err error) {
			if err != nil {
				dialog.ShowError(err, win)
				return
			}
			if readCloser == nil {
				return
			} // User cancelled

			sourceItem = readCloser.URI() // Store the URI
			sourceEntry.SetText(sourceItem.Path())
			readCloser.Close() // Important

			// Auto-fill torrent name if not manually set
			if torrentNameEntry.Text == "MyNewTorrent" || torrentNameEntry.Text == "" {
				baseName := filepath.Base(sourceItem.Path())
				// If it's a common archive, try to use name before extension
				ext := filepath.Ext(baseName)
				if ext != "" && (strings.EqualFold(ext, ".zip") || strings.EqualFold(ext, ".rar") || strings.EqualFold(ext, ".tar") || strings.EqualFold(ext, ".gz") || strings.EqualFold(ext, ".iso")) {
					baseName = strings.TrimSuffix(baseName, ext)
				}
				torrentNameEntry.SetText(baseName)
			}

		}, win)
		openDialog.Show()
	})

	// Create form items for the dialog
	formItems := []*widget.FormItem{
		widget.NewFormItem("Source", container.NewBorder(nil, nil, nil, browseButton, sourceEntry)),
		widget.NewFormItem("Torrent Name", torrentNameEntry),
		widget.NewFormItem("Piece Size", pieceSizeSelect),
		widget.NewFormItem("Tracker URLs", announceEntry),
	}

	// Create the dialog with form
	mainDialog := dialog.NewForm("Create New Torrent", "Create", "Cancel", formItems, func(create bool) {
		if !create {
			return
		}

		// Validate inputs
		if sourceItem == nil {
			dialog.ShowError(fmt.Errorf("source path cannot be empty"), win)
			return
		}
		finalTorrentName := strings.TrimSpace(torrentNameEntry.Text)
		if finalTorrentName == "" {
			dialog.ShowError(fmt.Errorf("torrent name cannot be empty"), win)
			return
		}
		finalAnnounceURLsRaw := announceEntry.Text
		// Split by newline or comma, then trim space and filter empty
		var finalAnnounceList []string
		urlCandidates := strings.FieldsFunc(finalAnnounceURLsRaw, func(r rune) bool { return r == '\n' || r == ',' })
		for _, u := range urlCandidates {
			trimmedU := strings.TrimSpace(u)
			if trimmedU != "" {
				// Basic URL validation attempt
				if _, err := url.ParseRequestURI(trimmedU); err == nil {
					finalAnnounceList = append(finalAnnounceList, trimmedU)
				} else {
					log.Printf("Ignoring invalid tracker URL: %s (parse error: %v)", trimmedU, err)
				}
			}
		}
		if len(finalAnnounceList) == 0 {
			dialog.ShowInformation("No Trackers", "Warning: No valid tracker URLs provided. The torrent will be 'trackerless' (DHT/PEX only, if supported) or rely on manual peer addition.", win)
		}

		// Ask where to save the .torrent file
		saveDialog := dialog.NewFileSave(func(writer fyne.URIWriteCloser, err error) {
			if err != nil {
				dialog.ShowError(err, win)
				return
			}
			if writer == nil {
				return
			} // User cancelled save dialog

			torrentOutputURI := writer.URI()
			writer.Close() // Close the writer from dialog, we'll open our own file

			torrentOutputPath := torrentOutputURI.Path()
			// Ensure it has .torrent extension
			if !strings.HasSuffix(strings.ToLower(torrentOutputPath), ".torrent") {
				torrentOutputPath += ".torrent"
			}

			// Create progress dialog
			progDialog := dialog.NewProgressInfinite("Creating Torrent",
				fmt.Sprintf("Processing '%s'...", filepath.Base(sourceItem.Path())), win)

			// Show the progress dialog
			progDialog.Show()

			// Keep a reference for later use
			pd := progDialog

			// Generate the torrent file in a background goroutine
			go func() {
				// Long-running operation to create the torrent file
				meta, err := generateTorrentFile(sourceItem.Path(), torrentOutputPath, finalTorrentName, pieceSize, finalAnnounceList)
				// Hide the progress dialog
				pd.Hide()

				if err != nil {
					dialog.ShowError(fmt.Errorf("Failed to create torrent: %w", err), win)
				} else {
					dialog.ShowInformation("Success",
						"Torrent file created successfully:\n"+torrentOutputPath, win)

					// Load source data for seeding
					sourceData, loadErr := loadSourceDataForSeeding(sourceItem.Path(), meta)
					if loadErr != nil {
						dialog.ShowError(fmt.Errorf("Failed to load source data for seeding: %w", loadErr), win)
						return
					}

					// Create a new ActiveTorrent instance for seeding
					var seedPeerID [20]byte
					if _, randErr := rand.Read(seedPeerID[:]); randErr != nil {
						dialog.ShowError(fmt.Errorf("Failed to generate PeerID for seeding: %w", randErr), win)
						return
					}

					seedActiveTorrent := &ActiveTorrent{
						PeerID:                seedPeerID,
						Meta:                  meta, // Store the full metadata
						Name:                  meta.Name,
						InfoHash:              meta.InfoHash,
						PieceHashes:           meta.PieceHashes,
						PieceLength:           meta.PieceLength,
						TotalLength:           meta.Length,
						Files:                 meta.Files,
						IsSingleFile:          meta.IsSingleFile,
						downloadPath:          sourceItem.Path(), // Path to original data
						dataBuffer:            sourceData,        // Loaded data
						statusBinding:         binding.NewString(),
						uploadSpeedBinding:    binding.NewString(),
						peersConnectedBinding: binding.NewInt(),
						progressBinding:       binding.NewFloat(), // For seeding, progress is 100%
						etaBinding:            binding.NewString(),
						totalPieces:           len(meta.PieceHashes),
						pieceDownloaded:       make(Bitfield, (len(meta.PieceHashes)+7)/8),
						downloadedPiecesCount: len(meta.PieceHashes), // All pieces are present
					}
					_ = seedActiveTorrent.statusBinding.Set(StatusSeeding)
					_ = seedActiveTorrent.uploadSpeedBinding.Set(formatSpeed(0))
					_ = seedActiveTorrent.peersConnectedBinding.Set(0)
					_ = seedActiveTorrent.progressBinding.Set(1.0) // 100%
					_ = seedActiveTorrent.etaBinding.Set("Seeding")

					// Mark all pieces as downloaded for the seeder's bitfield
					for i := 0; i < seedActiveTorrent.totalPieces; i++ {
						seedActiveTorrent.pieceDownloaded.SetPiece(i)
					}

					// Create a new window for seeding status
					seedWindow := globalTorrentManager.fyneApp.NewWindow("Seeding: " + meta.Name)
					nameLabel := widget.NewLabel("Torrent: " + seedActiveTorrent.Name)
					statusLabel := widget.NewLabel("")
					statusLabel.Bind(seedActiveTorrent.statusBinding)
					uploadSpeedLabel := widget.NewLabel("")
					uploadSpeedLabel.Bind(seedActiveTorrent.uploadSpeedBinding)
					peersLabel := widget.NewLabel("")
					peersLabel.Bind(binding.IntToStringWithFormat(seedActiveTorrent.peersConnectedBinding, "Peers: %d"))

					// Add stop seeding button
					stopButton := widget.NewButton("Stop Seeding", func() {
						seedActiveTorrent.StopSeeding()
						seedWindow.Close()
					})

					// Add info about the torrent
					infoLabel := widget.NewLabel(fmt.Sprintf("Size: %s\nPieces: %d\nPiece Size: %s",
						formatSize(meta.Length),
						len(meta.PieceHashes),
						formatSize(meta.PieceLength)))

					// Add tracker info
					trackerLabel := widget.NewLabel("")
					if meta.Announce != "" {
						trackerLabel.SetText("Primary Tracker: " + meta.Announce)
					}

					// Create a progress bar (always at 100% for seeding)
					progressBar := widget.NewProgressBar()
					progressBar.SetValue(1.0)
					progressBar.TextFormatter = func() string { return "100%" }

					seedWindow.SetContent(container.NewVBox(
						nameLabel,
						statusLabel,
						progressBar,
						uploadSpeedLabel,
						peersLabel,
						infoLabel,
						trackerLabel,
						stopButton,
					))
					seedWindow.Resize(fyne.NewSize(450, 250))
					seedWindow.SetOnClosed(func() {
						seedActiveTorrent.StopSeeding()
					})
					seedWindow.Show()

					// Start seeding in a new goroutine
					go seedActiveTorrent.startSeeding()
				}
			}()
		}, win)
		saveDialog.SetFileName(finalTorrentName + ".torrent")
		saveDialog.Show()
	}, win)

	mainDialog.Resize(fyne.NewSize(500, 350)) // Make dialog a bit wider
	mainDialog.Show()
}

// createTorrentFunc has been removed as it was a duplicate of showCreateTorrentDialog

// loadSourceDataForSeeding reads the content of the source file(s) into a byte buffer.
func loadSourceDataForSeeding(sourceFsPath string, meta *TorrentMetadata) ([]byte, error) {
	if meta == nil {
		return nil, fmt.Errorf("metadata is nil, cannot load source data")
	}

	var dataBuffer bytes.Buffer // Use bytes.Buffer for efficient appending

	if meta.IsSingleFile {
		// For single file, sourceFsPath is the direct path to the file.
		fileData, err := os.ReadFile(sourceFsPath)
		if err != nil {
			return nil, fmt.Errorf("failed to read single file '%s': %w", sourceFsPath, err)
		}
		dataBuffer.Write(fileData)
	} else {
		// For multi-file, sourceFsPath is the root directory of the torrent content.
		// meta.Files contains paths relative to this root.
		for _, fileInfo := range meta.Files {
			// Construct the full path to each file
			currentFilePathElements := append([]string{sourceFsPath}, fileInfo.Path...)
			currentFilePath := filepath.Join(currentFilePathElements...)

			fileData, err := os.ReadFile(currentFilePath)
			if err != nil {
				return nil, fmt.Errorf("failed to read file '%s' in multi-file torrent: %w", currentFilePath, err)
			}
			dataBuffer.Write(fileData)
		}
	}

	// Verify loaded data length matches torrent metadata
	if dataBuffer.Len() != meta.Length {
		return nil, fmt.Errorf("loaded data length %d does not match metadata total length %d", dataBuffer.Len(), meta.Length)
	}

	return dataBuffer.Bytes(), nil
}

func generateTorrentFile(sourcePath, torrentOutputPath, torrentName string, pieceSize int, announceURLs []string) (*TorrentMetadata, error) {
	bInfo := bencodeInfo{
		Name:        torrentName,
		PieceLength: pieceSize,
		Private:     0, // Public torrent
	}

	sourceStat, err := os.Stat(sourcePath)
	if err != nil {
		return nil, fmt.Errorf("could not access source path '%s': %w", sourcePath, err)
	}

	var pieceHashesBuilder strings.Builder

	if sourceStat.IsDir() {
		bInfo.Files = []BencodeFile{}
		var totalTorrentLength int64 = 0
		currentPieceBuffer := make([]byte, 0, pieceSize)

		err := filepath.Walk(sourcePath, func(path string, fInfo os.FileInfo, walkErr error) error {
			if walkErr != nil {
				return walkErr
			}
			if fInfo.IsDir() {
				return nil
			}

			relPath, err := filepath.Rel(sourcePath, path)
			if err != nil {
				return fmt.Errorf("failed to get relative path for '%s': %w", path, err)
			}
			relPath = filepath.ToSlash(relPath)
			pathComponents := strings.Split(relPath, "/")

			bInfo.Files = append(bInfo.Files, BencodeFile{
				Length: int(fInfo.Size()),
				Path:   pathComponents,
			})
			totalTorrentLength += fInfo.Size()

			file, err := os.Open(path)
			if err != nil {
				return fmt.Errorf("failed to open file '%s' for hashing: %w", path, err)
			}
			defer file.Close()

			readBuf := make([]byte, 32*1024)
			for {
				n, readErr := file.Read(readBuf)
				if n > 0 {
					currentPieceBuffer = append(currentPieceBuffer, readBuf[:n]...)
					for len(currentPieceBuffer) >= pieceSize {
						pieceToHash := currentPieceBuffer[:pieceSize]
						hash := sha1.Sum(pieceToHash)
						pieceHashesBuilder.Write(hash[:])
						currentPieceBuffer = currentPieceBuffer[pieceSize:]
					}
				}
				if readErr == io.EOF {
					break
				}
				if readErr != nil {
					return fmt.Errorf("error reading file '%s': %w", path, readErr)
				}
			}
			return nil
		})

		if err != nil {
			return nil, fmt.Errorf("error walking directory '%s': %w", sourcePath, err)
		}
		if len(currentPieceBuffer) > 0 {
			hash := sha1.Sum(currentPieceBuffer)
			pieceHashesBuilder.Write(hash[:])
		}
		// bInfo.Length is implicitly 0 for multi-file as per bencode spec (omitempty if Files is present)
	} else { // Single file torrent
		bInfo.Length = int(sourceStat.Size()) // Set 'length' for single file

		file, err := os.Open(sourcePath)
		if err != nil {
			return nil, fmt.Errorf("could not open file '%s' for hashing: %w", sourcePath, err)
		}
		defer file.Close()

		currentPieceBuffer := make([]byte, pieceSize)
		for {
			// ReadFull ensures buffer is filled, unless EOF or unexpected EOF occurs.
			n, readErr := io.ReadFull(file, currentPieceBuffer)
			if n > 0 { // Process bytes read, even if error occurred (e.g. last partial piece)
				hash := sha1.Sum(currentPieceBuffer[:n])
				pieceHashesBuilder.Write(hash[:])
			}
			if readErr == io.EOF || readErr == io.ErrUnexpectedEOF { // Expected end of file conditions
				break
			}
			if readErr != nil {
				return nil, fmt.Errorf("error reading file '%s' for hashing: %w", sourcePath, readErr)
			}
		}
	}

	bInfo.Pieces = pieceHashesBuilder.String()
	if bInfo.Pieces == "" && (bInfo.Length > 0 || len(bInfo.Files) > 0) {
		return nil, fmt.Errorf("no piece hashes generated, but torrent has data")
	}

	announceList := [][]string{}
	for _, url := range announceURLs {
		announceList = append(announceList, []string{url})
	}

	bTorrent := bencodeTorrent{
		Info:         bInfo,
		CreationDate: time.Now().Unix(),
		CreatedBy:    "Go Torrent Client GUI v0.1",
		Comment:      "Created with Go Torrent Client GUI",
	}
	if len(announceURLs) > 0 {
		bTorrent.Announce = announceURLs[0]
		if len(announceURLs) > 1 {
			bTorrent.AnnounceList = announceList
		}
	}

	// Convert to TorrentMetadata before writing file
	torrentMeta, err := btoToTorrentMetadata(&bTorrent)
	if err != nil {
		return nil, fmt.Errorf("could not convert to TorrentMetadata: %w", err)
	}

	// Write the bencoded structure to the output file
	outFile, err := os.Create(torrentOutputPath)
	if err != nil {
		return nil, fmt.Errorf("could not create output torrent file '%s': %w", torrentOutputPath, err)
	}
	defer outFile.Close()

	err = bencode.Marshal(outFile, bTorrent)
	if err != nil {
		return nil, fmt.Errorf("could not bencode torrent data to file: %w", err)
	}

	return torrentMeta, nil
}
