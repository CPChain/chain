package backend

import (
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

// RemoteValidator represents a remote signer waiting to be connected and communicate with.
type RemoteValidator struct {
	*RemoteSigner

	queuedPreprepareBlocks chan *types.Block  // Queue of blocks to broadcast to the signer
	queuedPrepareHeaders   chan *types.Header // Queue of signatures to broadcast to the signer
	queuedCommitHeaders    chan *types.Header // Queue of signatures to broadcast to the signer
	queuedValidateBlocks   chan *types.Block

	queuedPreprepareImpeachBlocks chan *types.Block
	queuedPrepareImpeachHeaders   chan *types.Header
	queuedCommitImpeachHeaders    chan *types.Header
	queuedValidateImpeachBlocks   chan *types.Block

	quitCh chan struct{} // Termination channel to stop the broadcaster

}

// NewRemoteValidator creates a new NewRemoteValidator with given view idx and address.
func NewRemoteValidator(address common.Address) *RemoteValidator {
	return &RemoteValidator{
		RemoteSigner: NewRemoteSigner(address),

		queuedPreprepareBlocks: make(chan *types.Block, maxQueuedBlocks),
		queuedPrepareHeaders:   make(chan *types.Header, maxQueuedHeaders),
		queuedCommitHeaders:    make(chan *types.Header, maxQueuedHeaders),
		queuedValidateBlocks:   make(chan *types.Block, maxQueuedBlocks),

		queuedPreprepareImpeachBlocks: make(chan *types.Block, maxQueuedBlocks),
		queuedPrepareImpeachHeaders:   make(chan *types.Header, maxQueuedHeaders),
		queuedCommitImpeachHeaders:    make(chan *types.Header, maxQueuedHeaders),
		queuedValidateImpeachBlocks:   make(chan *types.Block, maxQueuedBlocks),

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
		case block := <-s.queuedPreprepareBlocks:
			if err := s.SendPreprepareBlock(block); err != nil {

				log.Warn("failed to propagate generated block", "number", block.NumberU64(), "hash", block.Hash(), "err", err)

				return
			}
			log.Debug("Propagated generated block", "number", block.NumberU64(), "hash", block.Hash())

		case header := <-s.queuedPrepareHeaders:
			if err := s.SendPrepareHeader(header); err != nil {

				log.Warn("failed to propagate signed prepare header", "number", header.Number, "hash", header.Hash(), "err", err)

				return
			}
			log.Debug("Propagated signed prepare header", "number", header.Number, "hash", header.Hash())

		case header := <-s.queuedCommitHeaders:
			if err := s.SendCommitHeader(header); err != nil {

				log.Warn("failed to propagate signed commit header", "number", header.Number, "hash", header.Hash(), "err", err)

				return
			}
			log.Debug("Propagated signed commit header", "number", header.Number, "hash", header.Hash())

		case block := <-s.queuedValidateBlocks:
			if err := s.SendValidateBlock(block); err != nil {

				log.Warn("failed to propagate validate block", "number", block.NumberU64(), "hash", block.Hash(), "err", err)

				return
			}
			log.Debug("Propagated validate block", "number", block.NumberU64(), "hash", block.Hash())

		case block := <-s.queuedPreprepareImpeachBlocks:
			if err := s.SendPreprepareImpeachBlock(block); err != nil {
				return
			}
			log.Debug("Propagated generated impeach block", "number", block.Number(), "hash", block.Hash())

		case header := <-s.queuedPrepareImpeachHeaders:
			if err := s.SendPrepareImpeachHeader(header); err != nil {

				log.Warn("failed to propagate signed impeach prepare header", "number", header.Number, "hash", header.Hash(), "err", err)

				return
			}
			log.Debug("Propagated signed impeach prepare header", "number", header.Number, "hash", header.Hash())

		case header := <-s.queuedCommitImpeachHeaders:
			if err := s.SendCommitImpeachHeader(header); err != nil {

				log.Warn("failed to propagate signed impeach commit header", "number", header.Number, "hash", header.Hash(), "err", err)

				return
			}
			log.Debug("Propagated signed impeach commit header", "number", header.Number, "hash", header.Hash())

		case block := <-s.queuedValidateImpeachBlocks:
			if err := s.SendImpeachValidateBlock(block); err != nil {

				log.Warn("failed to propagate impeach validate block", "number", block.NumberU64(), "hash", block.Hash(), "err", err)

				return
			}
			log.Debug("Propagated impeach validate block", "number", block.NumberU64(), "hash", block.Hash())

		case <-s.quitCh:
			return
		}
	}
}

// SendNewSignerMsg sends a
func (s *RemoteValidator) SendNewSignerMsg(eb common.Address) error {
	return p2p.Send(s.rw, NewSignerMsg, eb)
}

// SendPreprepareBlock propagates an entire block to a remote peer.
func (s *RemoteValidator) SendPreprepareBlock(block *types.Block) error {
	return p2p.Send(s.rw, PreprepareBlockMsg, block)
}

// AsyncSendPreprepareBlock queues an entire block for propagation to a remote peer. If
// the peer's broadcast queue is full, the event is silently dropped.
func (s *RemoteValidator) AsyncSendPreprepareBlock(block *types.Block) {
	select {
	case s.queuedPreprepareBlocks <- block:
	default:
		log.Debug("Dropping block propagation", "number", block.NumberU64(), "hash", block.Hash())
	}
}

// SendPreprepareImpeachBlock propagates an entire block to a remote peer.
func (s *RemoteValidator) SendPreprepareImpeachBlock(block *types.Block) error {
	return p2p.Send(s.rw, PreprepareImpeachBlockMsg, block)
}

// AsyncSendPreprepareImpeachBlock queues an entire block for propagation to a remote peer. If
// the peer's broadcast queue is full, the event is silently dropped.
func (s *RemoteValidator) AsyncSendPreprepareImpeachBlock(block *types.Block) {
	select {
	case s.queuedPreprepareImpeachBlocks <- block:
	default:
		log.Debug("Dropping block propagation", "number", block.NumberU64(), "hash", block.Hash())
	}
}

// SendPrepareHeader sends new signed block header.
func (s *RemoteValidator) SendPrepareHeader(header *types.Header) error {
	err := p2p.Send(s.rw, PrepareHeaderMsg, header)
	return err
}

// AsyncSendPrepareHeader adds a msg to broadcast channel
func (s *RemoteValidator) AsyncSendPrepareHeader(header *types.Header) {
	select {
	case s.queuedPrepareHeaders <- header:
	default:
		log.Debug("Dropping signature propagation", "number", header.Number, "hash", header.Hash())
	}
}

// SendPrepareImpeachHeader sends new signed block header.
func (s *RemoteValidator) SendPrepareImpeachHeader(header *types.Header) error {
	err := p2p.Send(s.rw, PrepareImpeachHeaderMsg, header)
	return err
}

// AsyncSendPrepareImpeachHeader adds a msg to broadcast channel
func (s *RemoteValidator) AsyncSendPrepareImpeachHeader(header *types.Header) {
	select {
	case s.queuedPrepareImpeachHeaders <- header:
	default:
		log.Debug("Dropping signature propagation", "number", header.Number, "hash", header.Hash())
	}
}

// SendCommitHeader sends new signed block header.
func (s *RemoteValidator) SendCommitHeader(header *types.Header) error {
	err := p2p.Send(s.rw, CommitHeaderMsg, header)
	return err
}

// AsyncSendCommitHeader sends new signed block header.
func (s *RemoteValidator) AsyncSendCommitHeader(header *types.Header) {
	select {
	case s.queuedCommitHeaders <- header:
	default:
		log.Debug("Dropping signature propagation", "number", header.Number, "hash", header.Hash())
	}
}

// SendCommitImpeachHeader sends new signed block header.
func (s *RemoteValidator) SendCommitImpeachHeader(header *types.Header) error {
	err := p2p.Send(s.rw, CommitImpeachHeaderMsg, header)
	return err
}

// AsyncSendCommitImpeachHeader sends new signed block header.
func (s *RemoteValidator) AsyncSendCommitImpeachHeader(header *types.Header) {
	select {
	case s.queuedCommitImpeachHeaders <- header:
	default:
		log.Debug("Dropping signature propagation", "number", header.Number, "hash", header.Hash())
	}
}

// SendValidateBlock propagates an entire block to a remote peer.
func (s *RemoteValidator) SendValidateBlock(block *types.Block) error {
	return p2p.Send(s.rw, ValidateBlockMsg, block)
}

// AsyncSendValidateBlock queues an entire block for propagation to a remote peer. If
// the peer's broadcast queue is full, the event is silently dropped.
func (s *RemoteValidator) AsyncSendValidateBlock(block *types.Block) {
	select {
	case s.queuedValidateBlocks <- block:
	default:
		log.Debug("Dropping block propagation", "number", block.NumberU64(), "hash", block.Hash())
	}
}

// SendImpeachValidateBlock propagates an entire block to a remote peer.
func (s *RemoteValidator) SendImpeachValidateBlock(block *types.Block) error {
	return p2p.Send(s.rw, ValidateImpeachBlockMsg, block)
}

// AsyncSendImpeachValidateBlock queues an entire block for propagation to a remote peer. If
// the peer's broadcast queue is full, the event is silently dropped.
func (s *RemoteValidator) AsyncSendImpeachValidateBlock(block *types.Block) {
	select {
	case s.queuedValidateImpeachBlocks <- block:
	default:
		log.Debug("Dropping block propagation", "number", block.NumberU64(), "hash", block.Hash())
	}
}
