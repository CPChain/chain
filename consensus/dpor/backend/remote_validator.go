package backend

import (
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
)

const (
	maxQueuedPendingBlocks      = 8
	maxQueuedPendingBlockHashes = 8
	maxQueuedSigs               = 8

	handshakeTimeout = 5 * time.Second
)

// RemoteValidator represents a remote signer waiting to be connected and communicate with.
type RemoteValidator struct {
	*p2p.Peer
	rw      p2p.MsgReadWriter
	version int

	epochIdx      uint64
	pubkey        []byte
	nodeID        string
	address       common.Address
	dialed        bool // bool to show if i already connected to this signer.
	pubkeyFetched bool
	nodeIDFetched bool
	nodeIDUpdated bool // bool to show if i updated my nodeid encrypted with this signer's pubkey to the contract.

	queuedPendingBlocks chan *types.Block  // Queue of blocks to broadcast to the signer
	queuedPrepareSigs   chan *types.Header // Queue of signatures to broadcast to the signer
	queuedCommitSigs    chan *types.Header // Queue of signatures to broadcast to the signer

	quitCh chan struct{} // Termination channel to stop the broadcaster

	lock sync.RWMutex
}

// NewRemoteValidator creates a new NewRemoteValidator with given view idx and address.
func NewRemoteValidator(epochIdx uint64, address common.Address) *RemoteValidator {
	return &RemoteValidator{
		epochIdx: epochIdx,
		address:  address,

		queuedPendingBlocks: make(chan *types.Block, maxQueuedPendingBlocks),
		queuedPrepareSigs:   make(chan *types.Header, maxQueuedSigs),
		queuedCommitSigs:    make(chan *types.Header, maxQueuedSigs),

		quitCh: make(chan struct{}),
	}
}

func (s *RemoteValidator) disconnect(server *p2p.Server) error {
	s.lock.Lock()
	nodeID := s.nodeID
	s.lock.Unlock()

	node, err := discover.ParseNode(nodeID)
	if err != nil {
		return err
	}
	server.RemovePeer(node)
	return nil
}

// SetValidatorPeer sets a signer
func (s *RemoteValidator) SetValidatorPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter) error {
	s.lock.Lock()
	defer s.lock.Unlock()

	s.version, s.Peer, s.rw = version, p, rw

	return nil
}

// broadcastLoop is a write loop that multiplexes block propagations, announcements
// and transaction broadcasts into the remote peer. The goal is to have an async
// writer that does not lock up node internals.
func (s *RemoteValidator) broadcastLoop() {
	for {
		select {
		// blocks waiting for signatures
		case block := <-s.queuedPendingBlocks:
			if err := s.SendNewPendingBlock(block); err != nil {
				return
			}
			s.Log().Trace("Propagated generated block", "number", block.Number(), "hash", block.Hash())

		case header := <-s.queuedPrepareSigs:
			if err := s.SendPrepareSignedHeader(header); err != nil {
				return
			}
			s.Log().Trace("Propagated signed prepare header", "number", header.Number, "hash", header.Hash())

		case header := <-s.queuedCommitSigs:
			if err := s.SendCommitSignedHeader(header); err != nil {
				return
			}
			s.Log().Trace("Propagated signed commit header", "number", header.Number, "hash", header.Hash())

		case <-s.quitCh:
			return
		}
	}
}

// SendNewSignerMsg sends a
func (s *RemoteValidator) SendNewSignerMsg(eb common.Address) error {
	return p2p.Send(s.rw, NewValidatorMsg, eb)
}

// SendNewPendingBlock propagates an entire block to a remote peer.
func (s *RemoteValidator) SendNewPendingBlock(block *types.Block) error {
	return p2p.Send(s.rw, PrepreparePendingBlockMsg, block)
}

// AsyncSendNewPendingBlock queues an entire block for propagation to a remote peer. If
// the peer's broadcast queue is full, the event is silently dropped.
func (s *RemoteValidator) AsyncSendNewPendingBlock(block *types.Block) {
	select {
	case s.queuedPendingBlocks <- block:
	default:
		s.Log().Debug("Dropping block propagation", "number", block.NumberU64(), "hash", block.Hash())
	}
}

// SendPrepareSignedHeader sends new signed block header.
func (s *RemoteValidator) SendPrepareSignedHeader(header *types.Header) error {
	err := p2p.Send(s.rw, PrepareSignedHeaderMsg, header)
	return err
}

// AsyncSendPrepareSignedHeader adds a msg to broadcast channel
func (s *RemoteValidator) AsyncSendPrepareSignedHeader(header *types.Header) {
	select {
	case s.queuedPrepareSigs <- header:
	default:
		s.Log().Debug("Dropping signature propagation", "number", header.Number, "hash", header.Hash())
	}
}

// SendCommitSignedHeader sends new signed block header.
func (s *RemoteValidator) SendCommitSignedHeader(header *types.Header) error {
	err := p2p.Send(s.rw, CommitSignedHeaderMsg, header)
	return err
}

// AsyncSendCommitSignedHeader sends new signed block header.
func (s *RemoteValidator) AsyncSendCommitSignedHeader(header *types.Header) {
	select {
	case s.queuedCommitSigs <- header:
	default:
		s.Log().Debug("Dropping signature propagation", "number", header.Number, "hash", header.Hash())
	}
}

// ValidatorHandshake tries to handshake with remote validator
func ValidatorHandshake(p *p2p.Peer, rw p2p.MsgReadWriter, coinbase common.Address, verifyRemoteValidatorFn VerifyRemoteValidatorFn) (isValidator bool, address common.Address, err error) {
	// Send out own handshake in a new thread
	errc := make(chan error, 2)
	var validatorStatus ValidatorStatusData // safe to read after two values have been received from errc

	go func() {
		err := p2p.Send(rw, NewValidatorMsg, &ValidatorStatusData{
			ProtocolVersion: uint32(ProtocolVersion),
			Address:         coinbase,
		})
		errc <- err
	}()
	go func() {
		isValidator, address, err = ReadValidatorStatus(p, rw, &validatorStatus, verifyRemoteValidatorFn)
		errc <- err
	}()
	timeout := time.NewTimer(handshakeTimeout)
	defer timeout.Stop()
	for i := 0; i < 2; i++ {
		select {
		case err := <-errc:
			if err != nil {
				return false, common.Address{}, err
			}
		case <-timeout.C:
			return false, common.Address{}, p2p.DiscReadTimeout
		}
	}
	return isValidator, address, nil
}

// ReadValidatorStatus reads status of remote validator
func ReadValidatorStatus(p *p2p.Peer, rw p2p.MsgReadWriter, validatorStatus *ValidatorStatusData, verifyValidatorFn VerifyRemoteValidatorFn) (isValidator bool, address common.Address, err error) {
	msg, err := rw.ReadMsg()
	if err != nil {
		return false, common.Address{}, err
	}
	if msg.Code != NewValidatorMsg {
		return false, common.Address{}, errResp(ErrNoStatusMsg, "first msg has code %x (!= %x)", msg.Code, NewValidatorMsg)
	}
	if msg.Size > ProtocolMaxMsgSize {
		return false, common.Address{}, errResp(ErrMsgTooLarge, "%v > %v", msg.Size, ProtocolMaxMsgSize)
	}
	// Decode the handshake and make sure everything matches
	if err := msg.Decode(&validatorStatus); err != nil {
		return false, common.Address{}, errResp(ErrDecode, "msg %v: %v", msg, err)
	}
	if int(validatorStatus.ProtocolVersion) != ProtocolVersion {
		return false, common.Address{}, errResp(ErrProtocolVersionMismatch, "%d (!= %d)", validatorStatus.ProtocolVersion, ProtocolVersion)
	}

	// TODO: this (addr, ...) pair should be signed with its private key.
	// @liuq

	isValidator, err = verifyValidatorFn(validatorStatus.Address)
	return isValidator, validatorStatus.Address, err
}
