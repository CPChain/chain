package backend

import (
	"errors"
	"sync"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/signer_register"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

const (
	maxPendingBlocks = 256
)

var (
	// ErrUnknownHandlerMode is returnd if in an unknown mode
	ErrUnknownHandlerMode = errors.New("unknown dpor handler mode")

	// ErrFailToAddPendingBlock is returned if failed to add block to pending
	ErrFailToAddPendingBlock = errors.New("fail to add pending block")
)

// ValidatorHandler implements PbftHandler
type ValidatorHandler struct {
	mode HandlerMode

	term          uint64
	termLen       uint64
	maxInitNumber uint64

	nodeId   string
	coinbase common.Address

	server *p2p.Server
	rsaKey *rsakey.RsaKey

	knownBlocks *RecentBlocks

	// signer register contract related fields
	contractAddress    common.Address
	contractCaller     *ContractCaller
	contractInstance   *contract.SignerConnectionRegister
	contractTransactor *bind.TransactOpts

	signers map[common.Address]*RemoteValidator

	// previous stable pbft status
	snap *consensus.PbftStatus

	// this func is from dpor, to determine the state
	statusFn       StatusFn
	statusUpdateFn StatusUpdateFn

	getEmptyBlockFn GetEmptyBlockFn

	// those three funcs are methods from dpor, used for header verification and signing
	verifyHeaderFn  VerifyHeaderFn
	validateBlockFn ValidateBlockFn
	signHeaderFn    SignHeaderFn

	// this func is method from blockchain, used for inserting a block to chain
	insertChainFn InsertChainFn

	// this func is method from cpc/handler(ProtocolManager),
	// used for broadcasting a block to my normal peers
	broadcastBlockFn BroadcastBlockFn

	// this func is method from dpor, used for checking if a remote peer is signer
	validateSignerFn ValidateSignerFn

	pendingBlockCh chan *types.Block
	quitSync       chan struct{}

	dialed    bool
	available bool

	lock sync.RWMutex
}

// NewValidatorHandler creates a new ValidatorHandler
func NewValidatorHandler(config *configs.DporConfig, etherbase common.Address) *ValidatorHandler {
	vh := &ValidatorHandler{
		coinbase:        etherbase,
		contractAddress: config.Contracts["signer"],
		termLen:         config.TermLen,
		maxInitNumber:   config.MaxInitBlockNumber,
		signers:         make(map[common.Address]*RemoteValidator),
		knownBlocks:     NewKnownBlocks(),
		pendingBlockCh:  make(chan *types.Block),
		quitSync:        make(chan struct{}),
		dialed:          false,
		available:       false,
	}

	// TODO: fix this
	vh.mode = LBFTMode

	return vh
}

// Start starts pbft validator handler
func (vh *ValidatorHandler) Start() {

	// Dail all remote signers
	go vh.DialAll()

	// Broadcast mined pending block, including empty block
	go vh.PendingBlockBroadcastLoop()

	return
}

// Stop stops all
func (vh *ValidatorHandler) Stop() {

	close(vh.quitSync)

	return
}

// GetProtocol returns validator handler protocol
func (vh *ValidatorHandler) GetProtocol() consensus.Protocol {
	return vh
}

// NodeInfo returns validator node status
func (vh *ValidatorHandler) NodeInfo() interface{} {

	return vh.statusFn()
}

// Name returns protocol name
func (vh *ValidatorHandler) Name() string {
	return ProtocolName
}

// Version returns protocol version
func (vh *ValidatorHandler) Version() uint {
	return ProtocolVersion
}

// Length returns protocol max msg code
func (vh *ValidatorHandler) Length() uint64 {
	return ProtocolLength
}

// Available returns if handler is available
func (vh *ValidatorHandler) Available() bool {
	vh.lock.RLock()
	defer vh.lock.RUnlock()

	return vh.available
}

// AddPeer adds a p2p peer to local peer set
func (vh *ValidatorHandler) AddPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter) (string, bool, error) {
	coinbase := vh.Signer()
	validator := vh.validateSignerFn

	log.Debug("do handshaking with remote peer...")

	ok, address, err := Handshake(p, rw, coinbase, validator)
	if !ok || err != nil {
		log.Debug("failed to handshake in dpor", "err", err, "ok", ok)
		return "", ok, err
	}
	signer, err := vh.addSigner(version, p, rw, address)

	log.Debug("after add signer", "signer", signer.ID(), "err", err)
	for addr, s := range vh.signers {
		log.Debug("signers in handler", "addr", addr.Hex(), "id", s.ID())
	}

	return address.Hex(), true, err
}

// RemovePeer removes a p2p peer with its addr
func (vh *ValidatorHandler) RemovePeer(addr string) error {
	return vh.removeSigner(common.HexToAddress(addr))
}

// HandleMsg handles a msg of peer with id "addr"
func (vh *ValidatorHandler) HandleMsg(addr string, msg p2p.Msg) error {

	signer, ok := vh.signers[common.HexToAddress(addr)]
	if !ok {
		// TODO: return new err
		return nil
	}

	return vh.handleMsg(signer, msg)
}

func (vh *ValidatorHandler) addSigner(version int, p *p2p.Peer, rw p2p.MsgReadWriter, address common.Address) (*RemoteValidator, error) {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	// TODO: add lock here
	signer, ok := vh.signers[address]

	if !ok {
		// TODO: @liuq fix this
		signer = NewRemoteValidator(vh.term, address)
	}

	log.Debug("adding remote signer...", "signer", address.Hex())

	err := signer.SetSigner(version, p, rw)
	if err != nil {

		log.Debug("failed to set peer")
		return nil, err
	}

	go signer.signerBroadcast()

	vh.signers[address] = signer
	return signer, nil
}

func (vh *ValidatorHandler) removeSigner(signer common.Address) error {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	if _, ok := vh.signers[signer]; ok {
		delete(vh.signers, signer)
	}

	return nil
}

func (vh *ValidatorHandler) handleMsg(p *RemoteValidator, msg p2p.Msg) error {
	log.Debug("handling msg", "msg", msg.Code)

	if msg.Code == NewSignerMsg {
		return errResp(ErrExtraStatusMsg, "uncontrolled new signer message")
	}

	// TODO: @liuq fix this.
	switch vh.mode {
	case LBFTMode:
		return vh.handleLbftMsg(msg, p)
	case PBFTMode:
		return vh.handlePbftMsg(msg, p)
	default:
		return ErrUnknownHandlerMode
	}
}

// handleLbftMsg handles given msg with lbft (lightweighted bft) mode
func (vh *ValidatorHandler) handleLbftMsg(msg p2p.Msg, p *RemoteValidator) error {

	// TODO: @liuq fix this.
	switch {
	case msg.Code == PrepreparePendingBlockMsg:
		// sign the block and broadcast PrepareSignedHeaderMsg

		var block *types.Block
		if err := msg.Decode(&block); err != nil {
			return errResp(ErrDecode, "%v: %v", msg, err)
		}
		block.ReceivedAt = msg.ReceivedAt
		block.ReceivedFrom = p

		log.Debug("received preprepare block", "number", block.NumberU64(), "hash", block.Hash().Hex())

		localBlock, err := vh.GetPendingBlock(block.NumberU64())
		if localBlock != nil && err == nil && localBlock.Block != nil {
			if localBlock.Status == Inserted {
				// go h.broadcastBlockFn(localBlock.Block, true)
				return nil
			}
		}

		// Verify the block
		// if correct, sign it and broadcast as Prepare msg
		// verify header, if basic fields are correct, broadcast prepare msg
		switch err := vh.validateBlockFn(block); err {
		case nil:
			// basic fields are correct

			log.Debug("validated preprepare block", "number", block.NumberU64(), "hash", block.Hash().Hex())

			// sign the block
			header := block.Header()
			switch e := vh.signHeaderFn(header, consensus.Preprepared); e {
			case nil:

				log.Debug("signed preprepare header, adding to pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

				// add block to pending block cache of blockchain
				if err := vh.AddPendingBlock(block.WithSeal(header)); err != nil {
					return err
				}

				log.Debug("broadcasting signed prepare header to other signers", "number", block.NumberU64(), "hash", block.Hash().Hex())

				// broadcast prepare msg
				go vh.BroadcastPrepareSignedHeader(header)

				return nil

			default:

				// TODO: remove this
				go vh.BroadcastMinedBlock(block)

				log.Warn("err when signing header", "hash", header.Hash, "number", header.Number.Uint64(), "err", err)
				return e
			}

		default:
			log.Warn("err when validating block", "hash", block.Hash(), "number", block.NumberU64(), "err", err)
			return err
		}

	case msg.Code == PrepareSignedHeaderMsg:
		// add sigs to the header and broadcast, if ready to accept, accept

		// retrieve the header
		var header *types.Header
		if err := msg.Decode(&header); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		log.Debug("received signed prepare header", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

		// verify the signed header
		// if correct, insert the block into chain, broadcast it
		switch err := vh.verifyHeaderFn(header, consensus.Prepared); err {
		case nil:
			// with enough prepare sigs

			log.Debug("verified signed prepare header", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			block, err := vh.GetPendingBlock(header.Number.Uint64())
			if block == nil || block.Block == nil {
				// TODO: remove this line
				return nil
			}

			blk := block.Block.WithSeal(header)
			err = vh.AddPendingBlock(blk)
			if err != nil {
				// TODO: remove this
				return nil
			}

			log.Debug("inserting block to block chain", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			err = vh.insertChainFn(blk)
			if err != nil {
				log.Warn("err when inserting header", "hash", block.Hash(), "number", block.NumberU64(), "err", err)
				return err
			}

			log.Debug("broadcasting block to other peers", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			err = vh.UpdateBlockStatus(block.NumberU64(), Inserted)
			if err != nil {
				log.Warn("err when updating block status", "number", block.NumberU64(), "err", err)
				return err
			}

			// broadcast the block
			go vh.broadcastBlockFn(blk, true)

		case consensus.ErrNotEnoughSigs:
			// sign the block

			log.Debug("without enough sigs in siged prepare header", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			switch e := vh.signHeaderFn(header, consensus.Prepared); e {
			case nil:

				log.Debug("signed prepare header, broadcasting...", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

				go vh.BroadcastPrepareSignedHeader(header)

			default:

				// TODO: remove this
				block, err := vh.GetPendingBlock(header.Number.Uint64())
				if block != nil && block.Block != nil {
					vh.BroadcastMinedBlock(block.Block)
					return nil
				}

				log.Warn("err when signing header", "hash", header.Hash(), "number", header.Number.Uint64(), "err", err)
				return e
			}

		default:
			log.Warn("err when verifying header", "hash", header.Hash(), "number", header.Number.Uint64(), "err", err)
		}

	default:
		return consensus.ErrUnknownLbftState
	}
	return nil
}

func (vh *ValidatorHandler) handlePbftMsg(msg p2p.Msg, p *RemoteValidator) error {
	switch vh.statusFn().State {
	case consensus.NewRound:
		// if leader, send mined block with preprepare msg, enter preprepared
		// if not leader, wait for a new preprepare block, verify basic field, enter preprepared
		// if timer expired, send new empty block, enter preprepared

		vh.handlePreprepareMsg(msg, p)

	case consensus.Preprepared:

		// broadcast prepare msg

		// wait for enough(>2f+1, >2/3) prepare msg, if true, enter prepared
		vh.handlePrepareMsg(msg, p)

	case consensus.Prepared:

		// broadcast commit msg

		// wait for enough commit msg, if true, enter committed
		vh.handleCommitMsg(msg, p)

	case consensus.Committed:
		// insert block to chain, if succeed, enter finalcommitted

	case consensus.FinalCommitted:
		// broadcast block to normal peers, once finished, enter newround

	default:
		return consensus.ErrUnknownPbftState
	}

	return nil
}

// handlePreprepareMsg handles received preprepare msg
func (vh *ValidatorHandler) handlePreprepareMsg(msg p2p.Msg, p *RemoteValidator) error {
	switch {
	case msg.Code == PrepreparePendingBlockMsg:

		// recover the block
		var block *types.Block
		if err := msg.Decode(&block); err != nil {
			return errResp(ErrDecode, "%v: %v", msg, err)
		}
		block.ReceivedAt = msg.ReceivedAt
		block.ReceivedFrom = p

		// Verify the block
		// if correct, sign it and broadcast as Prepare msg
		header := block.RefHeader()

		// add block to pending block cache of blockchain
		if err := vh.AddPendingBlock(block); err != nil {
			return err
		}

		// TODO: add empty view change block verification here

		// verify header, if basic fields are correct, broadcast prepare msg
		switch err := vh.verifyHeaderFn(header, consensus.Preprepared); err {

		// basic fields are correct
		case nil:

			// sign the block
			switch e := vh.signHeaderFn(header, consensus.Preprepared); e {
			case nil:

				// broadcast prepare msg
				go vh.BroadcastPrepareSignedHeader(header)

				// update dpor status
				vh.statusUpdateFn()
				// now prepared

			default:
				return e
			}

		default:
			return err
		}

	default:
		log.Warn("receievd unwelcome msg in state Preprepare", "msg code", msg.Code)
	}
	return nil
}

func (vh *ValidatorHandler) handlePrepareMsg(msg p2p.Msg, p *RemoteValidator) error {
	switch {
	case msg.Code == PrepareSignedHeaderMsg:

		// retrieve the header
		var header *types.Header
		if err := msg.Decode(&header); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		// verify the signed header
		// if correct, rebroadcast it as Commit msg
		switch err := vh.verifyHeaderFn(header, consensus.Prepared); err {

		// with enough prepare sigs
		case nil:
			// sign the block
			switch e := vh.signHeaderFn(header, consensus.Prepared); e {
			case nil:

				// broadcast prepare msg
				go vh.BroadcastCommitSignedHeader(header)

				vh.statusUpdateFn()
				// now prepared

			default:
				return e
			}

		default:
		}

	default:
		log.Warn("receievd unwelcome msg in state Prepare", "msg code", msg.Code)
	}
	return nil
}

func (vh *ValidatorHandler) handleCommitMsg(msg p2p.Msg, p *RemoteValidator) error {
	switch {
	case msg.Code == CommitSignedHeaderMsg:

		// Verify the signed header
		// if correct, add the block to chain

		// retrieve the header
		var header *types.Header
		if err := msg.Decode(&header); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		switch err := vh.verifyHeaderFn(header, consensus.Committed); err {

		// with enough commit sigs
		case nil:

			// update dpor state and pbftstatus
			vh.statusUpdateFn()
			// now committed

			if block, err := vh.GetPendingBlock(header.Number.Uint64()); block != nil && err == nil {

				blk := block.WithSeal(header)

				// insert into chain
				if err := vh.insertChainFn(blk); err != nil {
					return err
				}

				// update dpor state and pbftstatus
				vh.statusUpdateFn()
				// now final-committed

				// broadcast the block
				go vh.broadcastBlockFn(blk, true)
				go vh.broadcastBlockFn(blk, false)

				// update dpor state and pbftstatus
				vh.statusUpdateFn()
				// now new-round

			}

		default:
		}

	default:
		log.Warn("receievd unwelcome msg in state Prepare", "msg code", msg.Code)
	}

	return nil
}

// ReadyToImpeach returns if its time to impeach leader
func (vh *ValidatorHandler) ReadyToImpeach() bool {
	snap := vh.snap
	head := vh.statusFn()

	if head.Head.Number.Uint64() <= snap.Head.Number.Uint64() {
		return true
	}

	vh.snap = head
	return false
}

// ReceiveMinedPendingBlock receives a block to add to pending block channel
func (vh *ValidatorHandler) ReceiveMinedPendingBlock(block *types.Block) error {
	select {
	case vh.pendingBlockCh <- block:
		err := vh.AddPendingBlock(block)
		if err != nil {
			return err
		}

		return nil
	}
}

// SetFuncs sets some funcs
func (vh *ValidatorHandler) SetFuncs(
	validateSignerFn ValidateSignerFn,
	verifyHeaderFn VerifyHeaderFn,
	verifyBlockFn ValidateBlockFn, signHeaderFn SignHeaderFn,
	broadcastBlockFn BroadcastBlockFn,
	insertChainFn InsertChainFn,
	statusFn StatusFn,
	statusUpdateFn StatusUpdateFn,
	getEmptyBlockFn GetEmptyBlockFn,
) error {

	vh.validateSignerFn = validateSignerFn
	vh.verifyHeaderFn = verifyHeaderFn
	vh.validateBlockFn = verifyBlockFn
	vh.signHeaderFn = signHeaderFn
	vh.broadcastBlockFn = broadcastBlockFn
	vh.insertChainFn = insertChainFn
	vh.statusFn = statusFn
	vh.statusUpdateFn = statusUpdateFn
	vh.getEmptyBlockFn = getEmptyBlockFn

	return nil
}

// Signer returns handler.signer
func (vh *ValidatorHandler) Signer() common.Address {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	return vh.coinbase
}

// SetSigner sets signer of handler
func (vh *ValidatorHandler) SetSigner(signer common.Address) {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	if vh.coinbase != signer {
		vh.coinbase = signer
	}
}

// IsAvailable returns if handler is available
func (vh *ValidatorHandler) IsAvailable() bool {
	vh.lock.RLock()
	defer vh.lock.RUnlock()

	return vh.available
}

// SetAvailable sets available
func (vh *ValidatorHandler) SetAvailable() {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	vh.available = true
}

// Disconnect disconnects all.
func (vh *ValidatorHandler) Disconnect() {
	vh.lock.Lock()
	connected, signers, server := vh.dialed, vh.signers, vh.server
	vh.lock.Unlock()

	if connected {
		log.Debug("disconnecting...")

		for _, s := range signers {
			err := s.disconnect(server)
			log.Debug("err when disconnect", "e", err)
		}

		vh.dialed = false
	}

	vh.lock.Lock()
	vh.dialed = connected
	vh.lock.Unlock()
}

// GetPendingBlock returns a pending block with given hash
func (vh *ValidatorHandler) GetPendingBlock(number uint64) (*KnownBlock, error) {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	block, err := vh.knownBlocks.GetKnownBlock(number)

	if err != nil {
		log.Debug("failed to get pending blocks", "number", number)
	}

	// log.Debug("got pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

	return block, err
}

// AddPendingBlock adds a pending block with given hash
func (vh *ValidatorHandler) AddPendingBlock(block *types.Block) error {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	log.Debug("adding block to pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

	err := vh.knownBlocks.AddBlock(block)
	return err
}

// UpdateBlockStatus updates known block status
func (vh *ValidatorHandler) UpdateBlockStatus(number uint64, status BlockStatus) error {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	log.Debug("updating block status", "number", number, "status", status)

	return vh.knownBlocks.UpdateStatus(number, status)
}
