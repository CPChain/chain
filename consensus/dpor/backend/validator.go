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
	ErrUnknownHandlerMode    = errors.New("unknown dpor handler mode")
	ErrFailToAddPendingBlock = errors.New("fail to add pending block")
)

// Handler implements PbftHandler
type Handler struct {
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

	signers map[common.Address]*Signer

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

// NewHandler creates a new Handler
func NewHandler(config *configs.DporConfig, etherbase common.Address) *Handler {
	h := &Handler{
		coinbase:        etherbase,
		contractAddress: config.Contracts["signer"],
		termLen:         config.TermLen,
		maxInitNumber:   config.MaxInitBlockNumber,
		signers:         make(map[common.Address]*Signer),
		knownBlocks:     NewKnownBlocks(),
		pendingBlockCh:  make(chan *types.Block),
		quitSync:        make(chan struct{}),
		dialed:          false,
		available:       false,
	}

	// TODO: fix this
	h.mode = LBFTMode

	return h
}

// Start starts pbft handler
func (h *Handler) Start() {

	// Dail all remote signers
	go h.DialAll()

	// Broadcast mined pending block, including empty block
	go h.PendingBlockBroadcastLoop()

	return
}

// Stop stops all
func (h *Handler) Stop() {

	close(h.quitSync)

	return
}

func (h *Handler) GetProtocol() consensus.Protocol {
	return h
}

func (h *Handler) NodeInfo() interface{} {

	return h.statusFn()
}

func (h *Handler) Name() string {
	return ProtocolName
}

func (h *Handler) Version() uint {
	return ProtocolVersion
}

func (h *Handler) Length() uint64 {
	return ProtocolLength
}

func (h *Handler) Available() bool {
	h.lock.RLock()
	defer h.lock.RUnlock()

	return h.available
}

func (h *Handler) AddPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter) (string, bool, error) {
	coinbase := h.Signer()
	validator := h.validateSignerFn

	log.Debug("do handshaking with remote peer...")

	ok, address, err := Handshake(p, rw, coinbase, validator)
	if !ok || err != nil {
		log.Debug("failed to handshake in dpor", "err", err, "ok", ok)
		return "", ok, err
	}
	signer, err := h.addSigner(version, p, rw, address)

	log.Debug("after add signer", "signer", signer.ID(), "err", err)
	for addr, s := range h.signers {
		log.Debug("signers in handler", "addr", addr.Hex(), "id", s.ID())
	}

	return address.Hex(), true, err
}

func (h *Handler) RemovePeer(addr string) error {
	return h.removeSigner(common.HexToAddress(addr))
}

func (h *Handler) HandleMsg(addr string, msg p2p.Msg) error {

	signer, ok := h.signers[common.HexToAddress(addr)]
	if !ok {
		// TODO: return new err
		return nil
	}

	return h.handleMsg(signer, msg)
}

func (h *Handler) addSigner(version int, p *p2p.Peer, rw p2p.MsgReadWriter, address common.Address) (*Signer, error) {
	h.lock.Lock()
	defer h.lock.Unlock()

	// TODO: add lock here
	signer, ok := h.signers[address]

	if !ok {
		// TODO: @liuq fix this
		signer = NewSigner(h.term, address)
	}

	log.Debug("adding remote signer...", "signer", address.Hex())

	// if signer.Peer == nil {
	err := signer.SetSigner(version, p, rw)
	if err != nil {

		log.Debug("failed to set peer")
		return nil, err
	}
	// }

	go signer.signerBroadcast()

	h.signers[address] = signer
	return signer, nil
}

func (h *Handler) removeSigner(signer common.Address) error {
	h.lock.Lock()
	defer h.lock.Unlock()

	if _, ok := h.signers[signer]; ok {
		delete(h.signers, signer)
	}

	return nil
}

func (h *Handler) handleMsg(p *Signer, msg p2p.Msg) error {
	log.Debug("handling msg", "msg", msg.Code)

	if msg.Code == NewSignerMsg {
		return errResp(ErrExtraStatusMsg, "uncontrolled new signer message")
	}

	// TODO: @liuq fix this.
	switch h.mode {
	case LBFTMode:
		return h.handleLbftMsg(msg, p)
	case PBFTMode:
		return h.handlePbftMsg(msg, p)
	default:
		return ErrUnknownHandlerMode
	}
}

// handleLbftMsg handles given msg with lbft (lightweighted bft) mode
func (h *Handler) handleLbftMsg(msg p2p.Msg, p *Signer) error {

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

		localBlock, err := h.GetPendingBlock(block.NumberU64())
		if localBlock != nil && err == nil && localBlock.Block != nil {
			if localBlock.Status == Inserted {
				// go h.broadcastBlockFn(localBlock.Block, true)
				return nil
			}
		}

		// Verify the block
		// if correct, sign it and broadcast as Prepare msg
		// verify header, if basic fields are correct, broadcast prepare msg
		switch err := h.validateBlockFn(block); err {
		case nil:
			// basic fields are correct

			log.Debug("validated preprepare block", "number", block.NumberU64(), "hash", block.Hash().Hex())

			// sign the block
			header := block.Header()
			switch e := h.signHeaderFn(header, consensus.Preprepared); e {
			case nil:

				log.Debug("signed preprepare header, adding to pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

				// add block to pending block cache of blockchain
				if err := h.AddPendingBlock(block.WithSeal(header)); err != nil {
					return err
				}

				log.Debug("broadcasting signed prepare header to other signers", "number", block.NumberU64(), "hash", block.Hash().Hex())

				// broadcast prepare msg
				go h.BroadcastPrepareSignedHeader(header)

				return nil

			default:

				// TODO: remove this
				go h.BroadcastMinedBlock(block)

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
		switch err := h.verifyHeaderFn(header, consensus.Prepared); err {
		case nil:
			// with enough prepare sigs

			log.Debug("verified signed prepare header", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			block, err := h.GetPendingBlock(header.Number.Uint64())
			if block == nil || block.Block == nil {
				// TODO: remove this line
				return nil
			}

			blk := block.Block.WithSeal(header)
			err = h.AddPendingBlock(blk)
			if err != nil {
				// TODO: remove this
				return nil
			}

			log.Debug("inserting block to block chain", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			err = h.insertChainFn(blk)
			if err != nil {
				log.Warn("err when inserting header", "hash", block.Hash(), "number", block.NumberU64(), "err", err)
				return err
			}

			log.Debug("broadcasting block to other peers", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			err = h.UpdateBlockStatus(block.NumberU64(), Inserted)
			if err != nil {
				log.Warn("err when updating block status", "number", block.NumberU64(), "err", err)
				return err
			}

			// broadcast the block
			go h.broadcastBlockFn(blk, true)

		case consensus.ErrNotEnoughSigs:
			// sign the block

			log.Debug("without enough sigs in siged prepare header", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			switch e := h.signHeaderFn(header, consensus.Prepared); e {
			case nil:

				log.Debug("signed prepare header, broadcasting...", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

				go h.BroadcastPrepareSignedHeader(header)

			default:

				// TODO: remove this
				block, err := h.GetPendingBlock(header.Number.Uint64())
				if block != nil && block.Block != nil {
					h.BroadcastMinedBlock(block.Block)
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

func (h *Handler) handlePbftMsg(msg p2p.Msg, p *Signer) error {
	switch h.statusFn().State {
	case consensus.NewRound:
		// if leader, send mined block with preprepare msg, enter preprepared
		// if not leader, wait for a new preprepare block, verify basic field, enter preprepared
		// if timer expired, send new empty block, enter preprepared

		h.handlePreprepareMsg(msg, p)

	case consensus.Preprepared:

		// broadcast prepare msg

		// wait for enough(>2f+1, >2/3) prepare msg, if true, enter prepared
		h.handlePrepareMsg(msg, p)

	case consensus.Prepared:

		// broadcast commit msg

		// wait for enough commit msg, if true, enter committed
		h.handleCommitMsg(msg, p)

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
func (h *Handler) handlePreprepareMsg(msg p2p.Msg, p *Signer) error {
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
		if err := h.AddPendingBlock(block); err != nil {
			return err
		}

		// TODO: add empty view change block verification here

		// verify header, if basic fields are correct, broadcast prepare msg
		switch err := h.verifyHeaderFn(header, consensus.Preprepared); err {

		// basic fields are correct
		case nil:

			// sign the block
			switch e := h.signHeaderFn(header, consensus.Preprepared); e {
			case nil:

				// broadcast prepare msg
				go h.BroadcastPrepareSignedHeader(header)

				// update dpor status
				h.statusUpdateFn()
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

func (h *Handler) handlePrepareMsg(msg p2p.Msg, p *Signer) error {
	switch {
	case msg.Code == PrepareSignedHeaderMsg:

		// retrieve the header
		var header *types.Header
		if err := msg.Decode(&header); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		// verify the signed header
		// if correct, rebroadcast it as Commit msg
		switch err := h.verifyHeaderFn(header, consensus.Prepared); err {

		// with enough prepare sigs
		case nil:
			// sign the block
			switch e := h.signHeaderFn(header, consensus.Prepared); e {
			case nil:

				// broadcast prepare msg
				go h.BroadcastCommitSignedHeader(header)

				h.statusUpdateFn()
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

func (h *Handler) handleCommitMsg(msg p2p.Msg, p *Signer) error {
	switch {
	case msg.Code == CommitSignedHeaderMsg:

		// Verify the signed header
		// if correct, add the block to chain

		// retrieve the header
		var header *types.Header
		if err := msg.Decode(&header); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		switch err := h.verifyHeaderFn(header, consensus.Committed); err {

		// with enough commit sigs
		case nil:

			// update dpor state and pbftstatus
			h.statusUpdateFn()
			// now committed

			if block, err := h.GetPendingBlock(header.Number.Uint64()); block != nil && err == nil {

				blk := block.WithSeal(header)

				// insert into chain
				if err := h.insertChainFn(blk); err != nil {
					return err
				}

				// update dpor state and pbftstatus
				h.statusUpdateFn()
				// now final-committed

				// broadcast the block
				go h.broadcastBlockFn(blk, true)
				go h.broadcastBlockFn(blk, false)

				// update dpor state and pbftstatus
				h.statusUpdateFn()
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
func (h *Handler) ReadyToImpeach() bool {
	snap := h.snap
	head := h.statusFn()

	if head.Head.Number.Uint64() <= snap.Head.Number.Uint64() {
		return true
	}

	h.snap = head
	return false
}

// ReceiveMinedPendingBlock receives a block to add to pending block channel
func (h *Handler) ReceiveMinedPendingBlock(block *types.Block) error {
	select {
	case h.pendingBlockCh <- block:
		err := h.AddPendingBlock(block)
		if err != nil {
			return err
		}

		return nil
	}
}

// SetFuncs sets some funcs
func (h *Handler) SetFuncs(
	validateSignerFn ValidateSignerFn,
	verifyHeaderFn VerifyHeaderFn,
	verifyBlockFn ValidateBlockFn, signHeaderFn SignHeaderFn,
	broadcastBlockFn BroadcastBlockFn,
	insertChainFn InsertChainFn,
	statusFn StatusFn,
	statusUpdateFn StatusUpdateFn,
	getEmptyBlockFn GetEmptyBlockFn,
) error {

	h.validateSignerFn = validateSignerFn
	h.verifyHeaderFn = verifyHeaderFn
	h.validateBlockFn = verifyBlockFn
	h.signHeaderFn = signHeaderFn
	h.broadcastBlockFn = broadcastBlockFn
	h.insertChainFn = insertChainFn
	h.statusFn = statusFn
	h.statusUpdateFn = statusUpdateFn
	h.getEmptyBlockFn = getEmptyBlockFn

	return nil
}

// Signer returns handler.signer
func (h *Handler) Signer() common.Address {
	h.lock.Lock()
	defer h.lock.Unlock()

	return h.coinbase
}

// SetSigner sets signer of handler
func (h *Handler) SetSigner(signer common.Address) {
	h.lock.Lock()
	defer h.lock.Unlock()

	if h.coinbase != signer {
		h.coinbase = signer
	}
}

// IsAvailable returns if handler is available
func (h *Handler) IsAvailable() bool {
	h.lock.RLock()
	defer h.lock.RUnlock()

	return h.available
}

// SetAvailable sets available
func (h *Handler) SetAvailable() {
	h.lock.Lock()
	defer h.lock.Unlock()

	h.available = true
}

// Disconnect disconnects all.
func (h *Handler) Disconnect() {
	h.lock.Lock()
	connected, signers, server := h.dialed, h.signers, h.server
	h.lock.Unlock()

	if connected {
		log.Debug("disconnecting...")

		for _, s := range signers {
			err := s.disconnect(server)
			log.Debug("err when disconnect", "e", err)
		}

		h.dialed = false
	}

	h.lock.Lock()
	h.dialed = connected
	h.lock.Unlock()
}

// GetPendingBlock returns a pending block with given hash
func (h *Handler) GetPendingBlock(number uint64) (*KnownBlock, error) {
	h.lock.Lock()
	defer h.lock.Unlock()

	block, err := h.knownBlocks.GetKnownBlock(number)

	if err != nil {
		log.Debug("failed to get pending blocks", "number", number)
	}

	// log.Debug("got pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

	return block, err
}

// AddPendingBlock adds a pending block with given hash
func (h *Handler) AddPendingBlock(block *types.Block) error {
	h.lock.Lock()
	defer h.lock.Unlock()

	log.Debug("adding block to pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

	err := h.knownBlocks.AddBlock(block)
	return err
}

func (h *Handler) UpdateBlockStatus(number uint64, status BlockStatus) error {
	h.lock.Lock()
	defer h.lock.Unlock()

	log.Debug("updating block status", "number", number, "status", status)

	return h.knownBlocks.UpdateStatus(number, status)
}
