package backend

import (
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

// RemoteValidator represents a remote signer waiting to be connected and communicate with.
type RemoteValidator struct {
	*RemoteSigner

	queuedPendingBlocks chan *types.Block  // Queue of blocks to broadcast to the signer
	queuedPrepareSigs   chan *types.Header // Queue of signatures to broadcast to the signer
	queuedCommitSigs    chan *types.Header // Queue of signatures to broadcast to the signer

	quitCh chan struct{} // Termination channel to stop the broadcaster

}

// NewRemoteValidator creates a new NewRemoteValidator with given view idx and address.
func NewRemoteValidator(epochIdx uint64, address common.Address) *RemoteValidator {
	return &RemoteValidator{
		RemoteSigner: NewRemoteSigner(epochIdx, address),

		queuedPendingBlocks: make(chan *types.Block, maxQueuedPendingBlocks),
		queuedPrepareSigs:   make(chan *types.Header, maxQueuedSigs),
		queuedCommitSigs:    make(chan *types.Header, maxQueuedSigs),

		quitCh: make(chan struct{}),
	}
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
	return p2p.Send(s.rw, NewSignerMsg, eb)
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
