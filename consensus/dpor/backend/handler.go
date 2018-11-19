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
	"github.com/ethereum/go-ethereum/p2p/discover"
)

var (
	// ErrUnknownHandlerMode is returnd if in an unknown mode
	ErrUnknownHandlerMode = errors.New("unknown dpor handler mode")
)

// Handler implements PbftHandler
type Handler struct {
	mode HandlerMode

	epochIdx    uint64
	epochLength uint64

	nodeId   string
	coinbase common.Address

	server *p2p.Server
	rsaKey *rsakey.RsaKey

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

	// those two funcs are methods from blockchain, to add and get pending
	// blocks from pending block cache of blockchain
	addPendingFn AddPendingBlockFn
	getPendingFn GetPendingBlockFn

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

	currentPending common.Hash

	dialed    bool
	available bool

	lock sync.RWMutex
}

// NewHandler creates a new Handler
func NewHandler(config *configs.DporConfig, etherbase common.Address) *Handler {
	h := &Handler{
		coinbase:        etherbase,
		contractAddress: config.Contracts["signer"],
		epochLength:     config.Epoch,
		signers:         make(map[common.Address]*Signer),
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

// Protocol returns a p2p protocol to handle dpor msgs
func (h *Handler) Protocol() p2p.Protocol {
	return p2p.Protocol{
		Name:    ProtocolName,
		Version: ProtocolVersion,
		Length:  ProtocolLength,
		Run: func(p *p2p.Peer, rw p2p.MsgReadWriter) error {

			if !h.IsAvailable() {
				log.Debug("not available now")
				return nil
			}
			log.Debug("available now!!!!!!!!")

			cb := h.Signer()
			validator := h.validateSignerFn

			log.Debug("handshaking...")
			ok, address, err := Handshake(p, rw, cb, validator)
			if !ok || err != nil {
				return err
			}

			log.Debug("done with handshake")

			select {
			case <-h.quitSync:
				return p2p.DiscQuitting
			default:
				return h.handle(ProtocolVersion, p, rw, address)
			}

		},
		NodeInfo: func() interface{} {
			return h.statusFn()
		},
		PeerInfo: func(id discover.NodeID) interface{} {
			return nil
		},
	}
}

func (h *Handler) handle(version int, p *p2p.Peer, rw p2p.MsgReadWriter, address common.Address) error {
	signer, err := h.addSigner(version, p, rw, address)
	if err != nil {
		return err
	}

	defer h.removeSigner(address)

	// main loop. handle incoming messages.
	for {
		if err := h.handleMsg(signer); err != nil {
			p.Log().Debug("Cpchain message handling failed", "err", err)
			return err
		}
	}
}

func (h *Handler) addSigner(version int, p *p2p.Peer, rw p2p.MsgReadWriter, address common.Address) (*Signer, error) {
	// TODO: add lock here
	signer, ok := h.signers[address]

	if !ok {
		// TODO: @liuq fix this
		signer = NewSigner(h.epochIdx, address)
	}

	log.Debug("received remote signer ping", "signer", address.Hex())

	if signer.Peer == nil {
		err := signer.SetSigner(version, p, rw)
		if err != nil {
			return nil, err
		}
	}
	return signer, nil
}

func (h *Handler) removeSigner(signer common.Address) error {

	if _, ok := h.signers[signer]; ok {
		delete(h.signers, signer)
	}

	return nil
}

func (h *Handler) handleMsg(p *Signer) error {
	log.Debug("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")

	// TODO: remove this. this is only for test
	block := h.getPendingFn(h.currentPending)
	if block != nil {
		p.SendNewPendingBlock(block)
	}
	// remove above

	msg, err := p.rw.ReadMsg()
	if err != nil {
		log.Debug("err when readmsg", "err", err)
		return err
	}
	if msg.Size > ProtocolMaxMsgSize {
		return errResp(ErrMsgTooLarge, "%v > %v", msg.Size, ProtocolMaxMsgSize)
	}
	defer msg.Discard()

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

		// Verify the block
		// if correct, sign it and broadcast as Prepare msg
		// verify header, if basic fields are correct, broadcast prepare msg
		switch err := h.validateBlockFn(block); err {
		case nil:
			// basic fields are correct

			// sign the block
			header := block.RefHeader()
			switch e := h.signHeaderFn(header, consensus.Preprepared); e {
			case nil:

				// add block to pending block cache of blockchain
				if err := h.addPendingFn(block); err != nil {
					return err
				}

				// broadcast prepare msg
				go h.BroadcastPrepareSignedHeader(header)

			default:
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

		// verify the signed header
		// if correct, insert the block into chain, broadcast it
		switch err := h.verifyHeaderFn(header, consensus.Prepared); err {
		case nil:
			// with enough prepare sigs
			// sign the block
			switch e := h.signHeaderFn(header, consensus.Prepared); e {
			case nil:

				block := h.getPendingFn(header.Hash())

				err := h.insertChainFn(block)
				if err != nil {
					log.Warn("err when inserting header", "hash", block.Hash(), "number", block.NumberU64(), "err", err)
					return err
				}

				// broadcast the block
				go h.broadcastBlockFn(block, true)

			default:
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
		if err := h.addPendingFn(block); err != nil {
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

			if block := h.getPendingFn(header.Hash()); block != nil {

				block = block.WithSeal(header)

				// insert into chain
				if err := h.insertChainFn(block); err != nil {
					return err
				}

				// update dpor state and pbftstatus
				h.statusUpdateFn()
				// now final-committed

				// broadcast the block
				go h.broadcastBlockFn(block, true)
				go h.broadcastBlockFn(block, false)

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
		log.Debug("!!!!!!!!!!!!!!!!! inserted into handler.pendingBlockCh")

		err := h.addPendingFn(block)
		log.Debug("err when add pending block to chain", "err", err)
		if err != nil {
			return err
		}
		h.currentPending = block.Hash()

		return nil
	}
}

// SetFuncs sets some funcs
func (h *Handler) SetFuncs(
	validateSignerFn ValidateSignerFn,
	verifyHeaderFn VerifyHeaderFn,
	verifyBlockFn ValidateBlockFn, signHeaderFn SignHeaderFn,
	addPendingBlockFn AddPendingBlockFn,
	getPendingBlockFn GetPendingBlockFn,
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
	h.addPendingFn = addPendingBlockFn
	h.getPendingFn = getPendingBlockFn
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
