package seeding

import (
	"context"
	"crypto/rand"
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

	"github.com/jackpal/bencode-go"
)

// Seeder manages the seeding process for a torrent
type Seeder struct {
	// Torrent metadata
	infoHash     [20]byte
	peerID       [20]byte
	pieceLength  int
	totalPieces  int
	totalLength  int64
	name         string
	isSingleFile bool
	files        []BencodeFile

	// File handling
	fileHandles []*os.File
	filePaths   []string

	// Network
	port            uint16
	listener        net.Listener
	announceURL     string
	trackerInterval int

	// Peer management
	peers    map[string]*PeerState
	peersMu  sync.RWMutex
	uploaded int64
	uploadMu sync.Mutex

	// Control
	ctx        context.Context
	cancelFunc context.CancelFunc
}

// PeerState tracks the state of a connected peer
type PeerState struct {
	conn           net.Conn
	peerID         [20]byte
	amChoking      bool
	amInterested   bool
	peerChoking    bool
	peerInterested bool
	bitfield       []byte
	lastActivity   time.Time
	uploaded       int64
}

// BencodeFile represents a file in a multi-file torrent
type BencodeFile struct {
	Length int64    `bencode:"length"`
	Path   []string `bencode:"path"`
}

// NewSeeder creates a new seeder for a torrent
func NewSeeder(announceURL string, port uint16) (*Seeder, error) {
	// Generate peer ID
	peerID := generatePeerID()
	log.Printf("Created new seeder with peer ID: %x", peerID)

	// Create context for cancellation
	ctx, cancel := context.WithCancel(context.Background())

	// Create seeder
	seeder := &Seeder{
		peerID:      peerID,
		port:        port,
		announceURL: announceURL,
		peers:       make(map[string]*PeerState),
		ctx:         ctx,
		cancelFunc:  cancel,
	}

	return seeder, nil
}

// SetTorrentInfo sets the torrent metadata and file information
func (s *Seeder) SetTorrentInfo(infoHash [20]byte, pieceLength int, totalPieces int, totalLength int64, name string, isSingleFile bool, files []BencodeFile) error {
	// Validate inputs
	if pieceLength <= 0 {
		return fmt.Errorf("invalid piece length: %d", pieceLength)
	}
	if totalPieces <= 0 {
		return fmt.Errorf("invalid total pieces: %d", totalPieces)
	}
	if totalLength <= 0 {
		return fmt.Errorf("invalid total length: %d", totalLength)
	}
	if name == "" {
		return fmt.Errorf("empty torrent name")
	}
	if !isSingleFile && len(files) == 0 {
		return fmt.Errorf("multi-file torrent must have at least one file")
	}

	// Validate file lengths in multi-file mode
	if !isSingleFile {
		var totalFileLength int64
		for i, f := range files {
			if f.Length <= 0 {
				return fmt.Errorf("invalid length for file %d: %d", i, f.Length)
			}
			if len(f.Path) == 0 {
				return fmt.Errorf("empty path for file %d", i)
			}
			totalFileLength += f.Length
		}
		if totalFileLength != totalLength {
			return fmt.Errorf("sum of file lengths (%d) does not match total length (%d)", totalFileLength, totalLength)
		}
	}

	s.infoHash = infoHash
	s.pieceLength = pieceLength
	s.totalPieces = totalPieces
	s.totalLength = totalLength
	s.name = name
	s.isSingleFile = isSingleFile
	s.files = files

	log.Printf("Set torrent info for %s:", name)
	log.Printf("  Info Hash: %x", infoHash)
	log.Printf("  Piece Length: %d bytes", pieceLength)
	log.Printf("  Total Pieces: %d", totalPieces)
	log.Printf("  Total Length: %d bytes", totalLength)
	log.Printf("  Is Single File: %v", isSingleFile)
	if !isSingleFile {
		log.Printf("  Files:")
		for _, f := range files {
			log.Printf("    - %s (%d bytes)", filepath.Join(f.Path...), f.Length)
		}
	}

	return nil
}

// SetFilePaths sets the paths to the files being seeded
func (s *Seeder) SetFilePaths(paths []string) error {
	// Validate paths
	if len(paths) == 0 {
		return fmt.Errorf("no file paths provided")
	}
	if s.isSingleFile && len(paths) != 1 {
		return fmt.Errorf("single file torrent must have exactly one file path")
	}
	if !s.isSingleFile && len(paths) != len(s.files) {
		return fmt.Errorf("number of file paths (%d) does not match number of files in torrent (%d)", len(paths), len(s.files))
	}

	// Verify files exist and are readable
	for i, path := range paths {
		info, err := os.Stat(path)
		if err != nil {
			return fmt.Errorf("failed to stat file %s: %w", path, err)
		}
		if info.IsDir() {
			return fmt.Errorf("path is a directory: %s", path)
		}
		if !s.isSingleFile && info.Size() != s.files[i].Length {
			return fmt.Errorf("file size mismatch for %s: got %d, want %d", path, info.Size(), s.files[i].Length)
		}
	}

	s.filePaths = paths
	log.Printf("Set file paths for seeding:")
	for _, path := range paths {
		log.Printf("  - %s", path)
	}
	return nil
}

// Start begins the seeding process
func (s *Seeder) Start() error {
	log.Printf("Starting seeder for %s on port %d", s.name, s.port)

	// Open files
	if err := s.openFiles(); err != nil {
		return fmt.Errorf("failed to open files: %w", err)
	}

	// Start TCP listener
	listener, err := net.Listen("tcp", fmt.Sprintf(":%d", s.port))
	if err != nil {
		return fmt.Errorf("failed to start listener: %w", err)
	}
	s.listener = listener
	log.Printf("Successfully started TCP listener on port %d", s.port)

	// Start tracker communication
	go s.trackerLoop()

	// Start accepting connections
	go s.acceptLoop()

	log.Printf("Started seeding torrent %s on port %d", s.name, s.port)
	return nil
}

// Stop stops the seeding process
func (s *Seeder) Stop() {
	if s.cancelFunc != nil {
		s.cancelFunc()
	}

	// Close listener
	if s.listener != nil {
		s.listener.Close()
	}

	// Close all peer connections
	s.peersMu.Lock()
	for _, peer := range s.peers {
		if peer.conn != nil {
			peer.conn.Close()
		}
	}
	s.peersMu.Unlock()

	// Close file handles
	for _, f := range s.fileHandles {
		f.Close()
	}

	// Announce stopped to tracker
	go s.announceToTracker("stopped")

	log.Printf("Stopped seeding torrent %s", s.name)
}

// openFiles opens all files needed for seeding
func (s *Seeder) openFiles() error {
	if len(s.filePaths) == 0 {
		return fmt.Errorf("no file paths set")
	}

	s.fileHandles = make([]*os.File, len(s.filePaths))
	for i, path := range s.filePaths {
		file, err := os.OpenFile(path, os.O_RDONLY, 0)
		if err != nil {
			// Close any already opened files
			for j := 0; j < i; j++ {
				s.fileHandles[j].Close()
			}
			return fmt.Errorf("failed to open file %s: %w", path, err)
		}
		s.fileHandles[i] = file
	}
	return nil
}

// trackerLoop periodically announces to the tracker
func (s *Seeder) trackerLoop() {
	// Initial announce
	if err := s.announceToTracker("started"); err != nil {
		log.Printf("Initial tracker announce failed: %v", err)
	}

	// Create ticker with a minimum interval
	interval := s.trackerInterval
	if interval <= 0 {
		interval = 1800 // Default to 30 minutes if no valid interval
	}
	ticker := time.NewTicker(time.Duration(interval) * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-s.ctx.Done():
			// Final announce
			if err := s.announceToTracker("stopped"); err != nil {
				log.Printf("Final tracker announce failed: %v", err)
			}
			return
		case <-ticker.C:
			if err := s.announceToTracker(""); err != nil {
				log.Printf("Periodic tracker announce failed: %v", err)
				// Don't exit the loop on error, just log it and continue
			}
		}
	}
}

// announceToTracker announces to the tracker
func (s *Seeder) announceToTracker(event string) error {
	// Build URL
	u, err := url.Parse(s.announceURL)
	if err != nil {
		return fmt.Errorf("invalid tracker URL: %w", err)
	}

	// Convert UDP tracker URLs to HTTP
	if u.Scheme == "udp" {
		u.Scheme = "http"
		// Remove the /announce suffix if present
		u.Path = strings.TrimSuffix(u.Path, "/announce")
	}

	// Add query parameters
	q := u.Query()
	q.Set("info_hash", string(s.infoHash[:]))
	q.Set("peer_id", string(s.peerID[:]))
	q.Set("port", strconv.Itoa(int(s.port)))
	q.Set("uploaded", strconv.FormatInt(s.uploaded, 10))
	q.Set("downloaded", "0") // We're seeding, so we've downloaded everything
	q.Set("left", "0")       // We're seeding, so we have everything
	q.Set("compact", "1")    // Request compact peer list
	if event != "" {
		q.Set("event", event)
	}
	u.RawQuery = q.Encode()

	log.Printf("Announcing to tracker %s with event %s", u.String(), event)

	// Make request
	resp, err := http.Get(u.String())
	if err != nil {
		return fmt.Errorf("failed to connect to tracker: %w", err)
	}
	defer resp.Body.Close()

	// Read response
	dict, err := bencode.Decode(resp.Body)
	if err != nil {
		return fmt.Errorf("failed to decode tracker response: %w", err)
	}

	// Parse response
	trackerResp, ok := dict.(map[string]interface{})
	if !ok {
		return fmt.Errorf("invalid tracker response format")
	}

	// Check for failure
	if failure, ok := trackerResp["failure reason"].(string); ok {
		return fmt.Errorf("tracker error: %s", failure)
	}

	// Get interval
	interval, ok := trackerResp["interval"].(int64)
	if !ok {
		return fmt.Errorf("missing interval in tracker response")
	}
	if interval <= 0 {
		// Use a default interval if the tracker returns an invalid one
		interval = 1800 // 30 minutes
		log.Printf("Warning: tracker returned invalid interval, using default of %d seconds", interval)
	}
	s.trackerInterval = int(interval)

	// Get peers
	peers, ok := trackerResp["peers"].(string)
	if !ok {
		return fmt.Errorf("missing peers in tracker response")
	}

	// Parse compact peer list
	for i := 0; i < len(peers); i += 6 {
		if i+6 > len(peers) {
			break
		}
		ip := net.IP(peers[i : i+4])
		port := binary.BigEndian.Uint16([]byte(peers[i+4 : i+6]))
		peerAddr := fmt.Sprintf("%s:%d", ip.String(), port)
		log.Printf("Received peer from tracker: %s", peerAddr)
	}

	log.Printf("Successfully announced to tracker. Interval: %d seconds", interval)
	return nil
}

// acceptLoop accepts incoming peer connections
func (s *Seeder) acceptLoop() {
	for {
		select {
		case <-s.ctx.Done():
			return
		default:
			conn, err := s.listener.Accept()
			if err != nil {
				if s.ctx.Err() != nil {
					return
				}
				log.Printf("Failed to accept connection: %v", err)
				continue
			}
			go s.handlePeerConnection(conn)
		}
	}
}

// handlePeerConnection manages a peer connection
func (s *Seeder) handlePeerConnection(conn net.Conn) {
	peerAddr := conn.RemoteAddr().String()
	log.Printf("New peer connection from %s", peerAddr)
	defer func() {
		log.Printf("Closing connection to peer %s", peerAddr)
		conn.Close()
	}()

	// Set read deadline
	conn.SetReadDeadline(time.Now().Add(30 * time.Second))

	// Send handshake
	handshake := make([]byte, 68)
	handshake[0] = 19 // pstrlen
	copy(handshake[1:20], "BitTorrent protocol")
	copy(handshake[28:48], s.infoHash[:])
	copy(handshake[48:68], s.peerID[:])
	if _, err := conn.Write(handshake); err != nil {
		log.Printf("Failed to send handshake to %s: %v", peerAddr, err)
		return
	}
	log.Printf("Sent handshake to %s", peerAddr)

	// Read peer's handshake
	resp := make([]byte, 68)
	if _, err := io.ReadFull(conn, resp); err != nil {
		log.Printf("Failed to read peer handshake from %s: %v", peerAddr, err)
		return
	}

	// Validate handshake
	if resp[0] != 19 || string(resp[1:20]) != "BitTorrent protocol" {
		log.Printf("Invalid protocol string in handshake from %s", peerAddr)
		return
	}

	// Validate info hash
	var peerInfoHash [20]byte
	copy(peerInfoHash[:], resp[28:48])
	if peerInfoHash != s.infoHash {
		log.Printf("Info hash mismatch in handshake from %s. Expected %x, got %x", peerAddr, s.infoHash, peerInfoHash)
		return
	}

	// Store peer ID
	var peerID [20]byte
	copy(peerID[:], resp[48:68])
	log.Printf("Received valid handshake from %s with peer ID %x", peerAddr, peerID)

	// Create peer state
	peer := &PeerState{
		conn:         conn,
		peerID:       peerID,
		amChoking:    true,
		amInterested: false,
		peerChoking:  true,
		lastActivity: time.Now(),
	}

	// Add to peers map
	s.peersMu.Lock()
	s.peers[peerAddr] = peer
	s.peersMu.Unlock()

	// Send bitfield (all pieces available)
	bitfield := make([]byte, (s.totalPieces+7)/8)
	for i := range bitfield {
		bitfield[i] = 0xFF
	}
	if err := s.sendMessage(conn, 5, bitfield); err != nil {
		log.Printf("Failed to send bitfield to %s: %v", peerAddr, err)
		return
	}
	log.Printf("Sent bitfield to %s", peerAddr)

	// Handle peer messages
	s.handlePeerMessages(peer)
}

// handlePeerMessages processes messages from a peer
func (s *Seeder) handlePeerMessages(peer *PeerState) {
	peerAddr := peer.conn.RemoteAddr().String()
	for {
		// Read message length
		lenBuf := make([]byte, 4)
		if _, err := io.ReadFull(peer.conn, lenBuf); err != nil {
			if s.ctx.Err() != nil {
				return
			}
			log.Printf("Failed to read message length from %s: %v", peerAddr, err)
			return
		}
		length := binary.BigEndian.Uint32(lenBuf)

		// Keep-alive message
		if length == 0 {
			peer.lastActivity = time.Now()
			continue
		}

		// Read message ID and payload
		msgBuf := make([]byte, length)
		if _, err := io.ReadFull(peer.conn, msgBuf); err != nil {
			log.Printf("Failed to read message from %s: %v", peerAddr, err)
			return
		}

		// Process message
		msgID := msgBuf[0]
		payload := msgBuf[1:]

		log.Printf("Received message from %s: ID=%d, Length=%d", peerAddr, msgID, length)

		switch msgID {
		case 0: // choke
			peer.peerChoking = true
			log.Printf("Peer %s choked us", peerAddr)
		case 1: // unchoke
			peer.peerChoking = false
			log.Printf("Peer %s unchoked us", peerAddr)
		case 2: // interested
			peer.peerInterested = true
			log.Printf("Peer %s is interested", peerAddr)
			if peer.amChoking {
				// Unchoke the peer
				if err := s.sendMessage(peer.conn, 1, nil); err != nil {
					log.Printf("Failed to send unchoke to %s: %v", peerAddr, err)
					return
				}
				peer.amChoking = false
				log.Printf("Unchoked peer %s", peerAddr)
			}
		case 3: // not interested
			peer.peerInterested = false
			log.Printf("Peer %s is not interested", peerAddr)
		case 4: // have
			if len(payload) != 4 {
				log.Printf("Invalid have message length from %s", peerAddr)
				return
			}
			pieceIndex := binary.BigEndian.Uint32(payload)
			if int(pieceIndex) >= s.totalPieces {
				log.Printf("Invalid piece index in have message from %s: %d", peerAddr, pieceIndex)
				return
			}
			// Update peer's bitfield
			byteIndex := pieceIndex / 8
			bitIndex := pieceIndex % 8
			if byteIndex < uint32(len(peer.bitfield)) {
				peer.bitfield[byteIndex] |= 1 << (7 - bitIndex)
			}
			log.Printf("Peer %s has piece %d", peerAddr, pieceIndex)
		case 5: // bitfield
			peer.bitfield = make([]byte, len(payload))
			copy(peer.bitfield, payload)
			log.Printf("Received bitfield from %s", peerAddr)
		case 6: // request
			if len(payload) != 12 {
				log.Printf("Invalid request message length from %s", peerAddr)
				return
			}
			if peer.amChoking {
				log.Printf("Ignoring request from choked peer %s", peerAddr)
				continue
			}
			pieceIndex := binary.BigEndian.Uint32(payload[0:4])
			begin := binary.BigEndian.Uint32(payload[4:8])
			length := binary.BigEndian.Uint32(payload[8:12])

			// Validate request
			if int(pieceIndex) >= s.totalPieces {
				log.Printf("Invalid piece index in request from %s: %d", peerAddr, pieceIndex)
				continue
			}
			if begin+length > uint32(s.pieceLength) {
				log.Printf("Invalid request length from %s: begin=%d, length=%d", peerAddr, begin, length)
				continue
			}
			if length > 16384 { // 16KB max
				log.Printf("Request too large from %s: %d", peerAddr, length)
				continue
			}

			log.Printf("Received request from %s: piece=%d, begin=%d, length=%d", peerAddr, pieceIndex, begin, length)

			// Read and send piece
			data, err := s.readBlock(int(pieceIndex), int(begin), int(length))
			if err != nil {
				log.Printf("Failed to read block for %s: %v", peerAddr, err)
				continue
			}

			// Construct piece message
			pieceMsg := make([]byte, 9+len(data))
			binary.BigEndian.PutUint32(pieceMsg[0:4], pieceIndex)
			binary.BigEndian.PutUint32(pieceMsg[4:8], begin)
			copy(pieceMsg[8:], data)

			if err := s.sendMessage(peer.conn, 7, pieceMsg); err != nil {
				log.Printf("Failed to send piece to %s: %v", peerAddr, err)
				return
			}

			// Update upload stats
			s.uploadMu.Lock()
			s.uploaded += int64(length)
			peer.uploaded += int64(length)
			s.uploadMu.Unlock()

			log.Printf("Sent piece to %s: piece=%d, begin=%d, length=%d", peerAddr, pieceIndex, begin, length)

		case 7: // piece (should not receive as seeder)
			log.Printf("Received unexpected piece message from %s", peerAddr)
		case 8: // cancel
			log.Printf("Received cancel message from %s", peerAddr)
		default:
			log.Printf("Unknown message ID %d from %s", msgID, peerAddr)
		}

		// Update last activity time
		peer.lastActivity = time.Now()
	}
}

// sendMessage sends a message to a peer
func (s *Seeder) sendMessage(conn net.Conn, id byte, payload []byte) error {
	length := uint32(1 + len(payload))
	msg := make([]byte, 4+1+len(payload))
	binary.BigEndian.PutUint32(msg[0:4], length)
	msg[4] = id
	copy(msg[5:], payload)
	_, err := conn.Write(msg)
	return err
}

// readBlock reads a block of data from the files
func (s *Seeder) readBlock(pieceIndex, begin, length int) ([]byte, error) {
	if pieceIndex < 0 || pieceIndex >= s.totalPieces {
		return nil, fmt.Errorf("invalid piece index: %d", pieceIndex)
	}

	// Calculate the absolute offset in the torrent
	pieceOffset := int64(pieceIndex) * int64(s.pieceLength)
	blockOffset := pieceOffset + int64(begin)

	// For single file torrents, it's simple
	if s.isSingleFile {
		if blockOffset+int64(length) > s.totalLength {
			return nil, fmt.Errorf("block extends beyond file end")
		}
		buf := make([]byte, length)
		_, err := s.fileHandles[0].ReadAt(buf, blockOffset)
		if err != nil {
			return nil, fmt.Errorf("failed to read block: %w", err)
		}
		return buf, nil
	}

	// For multi-file torrents, we need to find the right file and offset
	var currentOffset int64
	buf := make([]byte, length)
	bytesRead := 0

	for i, file := range s.files {
		fileEnd := currentOffset + file.Length
		if blockOffset >= currentOffset && blockOffset < fileEnd {
			// This file contains the start of our block
			fileOffset := blockOffset - currentOffset
			remainingInFile := file.Length - fileOffset
			toRead := int64(length - bytesRead)
			if toRead > remainingInFile {
				toRead = remainingInFile
			}

			_, err := s.fileHandles[i].ReadAt(buf[bytesRead:bytesRead+int(toRead)], fileOffset)
			if err != nil {
				return nil, fmt.Errorf("failed to read from file %s: %w", file.Path[len(file.Path)-1], err)
			}
			bytesRead += int(toRead)

			if bytesRead == length {
				return buf, nil
			}

			// Continue with next file if we need more data
			continue
		}
		currentOffset = fileEnd
	}

	if bytesRead != length {
		return nil, fmt.Errorf("failed to read complete block: got %d bytes, wanted %d", bytesRead, length)
	}

	return buf, nil
}

// generatePeerID generates a random peer ID
func generatePeerID() [20]byte {
	var peerID [20]byte
	peerID[0] = '-'
	peerID[1] = 'G'
	peerID[2] = 'O'
	peerID[3] = '0'
	peerID[4] = '0'
	peerID[5] = '0'
	peerID[6] = '1'
	peerID[7] = '-'
	// Fill the rest with random bytes
	rand.Read(peerID[8:])
	return peerID
}
