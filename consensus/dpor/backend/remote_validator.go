package backend

import (
	"context"
	"encoding/hex"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

// RemoteValidator represents a remote signer waiting to be connected and communicate with.
type RemoteValidator struct {
	*RemoteSigner

	pubkey        []byte
	nodeIDUpdated bool // bool to show if i updated my nodeid encrypted with this signer's pubkey to the contract.

	queuedPreprepareBlocks chan *types.Block  // Queue of blocks to broadcast to the signer
	queuedPrepareHeaders   chan *types.Header // Queue of signatures to broadcast to the signer
	queuedCommitHeaders    chan *types.Header // Queue of signatures to broadcast to the signer

	queuedPreprepareImpeachBlocks chan *types.Block
	queuedPrepareImpeachHeaders   chan *types.Header
	queuedCommitImpeachHeaders    chan *types.Header

	quitCh chan struct{} // Termination channel to stop the broadcaster

	validatorLock sync.RWMutex
}

// NewRemoteValidator creates a new NewRemoteValidator with given view idx and address.
func NewRemoteValidator(term uint64, address common.Address) *RemoteValidator {
	return &RemoteValidator{
		RemoteSigner: NewRemoteSigner(address),

		queuedPreprepareBlocks: make(chan *types.Block, maxQueuedBlocks),
		queuedPrepareHeaders:   make(chan *types.Header, maxQueuedHeaders),
		queuedCommitHeaders:    make(chan *types.Header, maxQueuedHeaders),

		queuedPreprepareImpeachBlocks: make(chan *types.Block, maxQueuedBlocks),
		queuedPrepareImpeachHeaders:   make(chan *types.Header, maxQueuedHeaders),
		queuedCommitImpeachHeaders:    make(chan *types.Header, maxQueuedHeaders),

		quitCh: make(chan struct{}),
	}
}

func (s *RemoteValidator) getPublicKey() []byte {
	s.validatorLock.RLock()
	defer s.validatorLock.RUnlock()

	return s.pubkey
}

// fetchPubkey fetches the public key of the remote validator from the contract.
func (s *RemoteValidator) fetchPubkey(contractInstance *contracts.ProposerRegister) error {

	address := s.Coinbase()

	log.Debug("fetching public key of remote signer")
	log.Debug("signer", "addr", address)

	pubkey, err := contractInstance.GetPublicKey(nil, address)
	if err != nil {
		return err
	}

	s.validatorLock.Lock()
	s.pubkey = pubkey
	s.validatorLock.Unlock()

	log.Debug("fetched public key of remote signer", "pubkey", pubkey)

	return nil
}

// uploadNodeID encrypts proposer's node id with this remote validator's public key and update to the contract.
func (s *RemoteValidator) uploadNodeID(term uint64, nodeID string, auth *bind.TransactOpts, contractInstance *contracts.ProposerRegister, client ClientBackend) error {
	validator := s.Coinbase()

	log.Debug("fetched rsa pubkey")
	log.Debug(hex.Dump(s.getPublicKey()))

	pubkey, err := rsakey.NewRsaPublicKey(s.getPublicKey())

	log.Debug("updating self nodeID with remote validator's public key")
	log.Debug("term", "term", term)
	log.Debug("validator", "addr", validator.Hex())
	log.Debug("proposer(me)", "addr", auth.From.Hex())
	log.Debug("nodeID", "nodeID", nodeID)
	log.Debug("pubkey", "pubkey", pubkey)

	if err != nil {
		return err
	}

	encryptedNodeID, err := pubkey.RsaEncrypt([]byte(nodeID))

	log.Debug("encryptedNodeID")
	log.Debug(hex.Dump(encryptedNodeID))

	transaction, err := contractInstance.AddNodeInfo(auth, big.NewInt(int64(term)), validator, encryptedNodeID)
	if err != nil {
		return err
	}

	ctx := context.Background()
	_, err = bind.WaitMined(ctx, client, transaction)
	if err != nil {
		return err
	}

	s.validatorLock.Lock()
	s.nodeIDUpdated = true
	s.validatorLock.Unlock()

	log.Debug("updated self nodeID")

	return nil
}

// UploadNodeInfo upload my nodeID the signer.
func (s *RemoteValidator) UploadNodeInfo(
	term uint64,
	nodeID string,
	auth *bind.TransactOpts,
	contractInstance *contracts.ProposerRegister,
	client ClientBackend,
) (bool, error) {

	log.Debug("dialing to remote signer", "signer", s)

	// fetch remote signer's public key if there is no one.
	if len(s.getPublicKey()) == 0 {
		err := s.fetchPubkey(contractInstance)
		if err != nil {
			log.Warn("err when fetching signer's pubkey from contract", "err", err)
			return false, err
		}
	}

	proposer := auth.From
	validator := s.Coinbase()

	nodeid, err := fetchNodeID(term, proposer, validator, contractInstance)
	if err != nil {
		return false, err
	}

	// update my nodeID to contract if already know the public key of the remote signer and not updated yet.
	if len(s.getPublicKey()) != 0 && len(nodeid) == 0 {
		err := s.uploadNodeID(term, nodeID, auth, contractInstance, client)
		if err != nil {
			log.Warn("err when updating my node id to contract", "err", err)
			return false, err
		}
	}

	nodeid, err = fetchNodeID(term, proposer, validator, contractInstance)
	if err != nil {
		return false, err
	}

	log.Debug("fetched node id", "nodeid", nodeid)

	return true, nil
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
				return
			}
			s.Log().Trace("Propagated generated block", "number", block.Number(), "hash", block.Hash())

		case block := <-s.queuedPreprepareImpeachBlocks:
			if err := s.SendPreprepareImpeachBlock(block); err != nil {
				return
			}
			s.Log().Trace("Propagated generated block", "number", block.Number(), "hash", block.Hash())

		case header := <-s.queuedPrepareHeaders:
			if err := s.SendPrepareHeader(header); err != nil {
				return
			}
			s.Log().Trace("Propagated signed prepare header", "number", header.Number, "hash", header.Hash())

		case header := <-s.queuedPrepareImpeachHeaders:
			if err := s.SendPrepareImpeachHeader(header); err != nil {
				return
			}
			s.Log().Trace("Propagated signed prepare header", "number", header.Number, "hash", header.Hash())

		case header := <-s.queuedCommitHeaders:
			if err := s.SendCommitHeader(header); err != nil {
				return
			}
			s.Log().Trace("Propagated signed commit header", "number", header.Number, "hash", header.Hash())

		case header := <-s.queuedCommitImpeachHeaders:
			if err := s.SendCommitImpeachHeader(header); err != nil {
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
		s.Log().Debug("Dropping block propagation", "number", block.NumberU64(), "hash", block.Hash())
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
		s.Log().Debug("Dropping block propagation", "number", block.NumberU64(), "hash", block.Hash())
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
		s.Log().Debug("Dropping signature propagation", "number", header.Number, "hash", header.Hash())
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
		s.Log().Debug("Dropping signature propagation", "number", header.Number, "hash", header.Hash())
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
		s.Log().Debug("Dropping signature propagation", "number", header.Number, "hash", header.Hash())
	}
}

// SendCommitImpeachHeader sends new signed block header.
func (s *RemoteValidator) SendCommitImpeachHeader(header *types.Header) error {
	err := p2p.Send(s.rw, CommitHeaderMsg, header)
	return err
}

// AsyncSendCommitImpeachHeader sends new signed block header.
func (s *RemoteValidator) AsyncSendCommitImpeachHeader(header *types.Header) {
	select {
	case s.queuedCommitImpeachHeaders <- header:
	default:
		s.Log().Debug("Dropping signature propagation", "number", header.Number, "hash", header.Hash())
	}
}
