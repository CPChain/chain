package backend

import (
	"context"
	"math/big"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/signerRegister"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
)

// Handler implements PbftHandler
type Handler struct {
	epochIdx uint64

	ownNodeID  string
	ownAddress common.Address

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
	verifyHeaderFn VerifyHeaderFn
	verifyBlockFn  VerifyBlockFn
	signHeaderFn   SignHeaderFn

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
		ownAddress:      etherbase,
		contractAddress: config.Contracts["signer"],
		signers:         make(map[common.Address]*Signer),
		pendingBlockCh:  make(chan *types.Block),
		quitSync:        make(chan struct{}),
		dialed:          false,
	}
	return h
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

// SetServer sets handler.server
func (h *Handler) SetServer(server *p2p.Server) error {
	h.lock.Lock()
	defer h.lock.Unlock()

	h.server = server
	h.ownNodeID = server.Self().String()

	return nil
}

// setRsaKey sets handler.rsaKey
func (h *Handler) setRsaKey(rsaReader RsaReader) error {
	h.lock.Lock()
	defer h.lock.Unlock()

	var err error
	h.rsaKey, err = rsaReader()

	return err
}

// SetContractCaller sets handler.contractcaller.
func (h *Handler) SetContractCaller(contractCaller *ContractCaller) error {

	// creates an contract instance
	contractInstance, err := contract.NewSignerConnectionRegister(h.contractAddress, contractCaller.Client)
	if err != nil {
		return err
	}

	// creates a keyed transactor
	auth := bind.NewKeyedTransactor(contractCaller.Key.PrivateKey)

	gasPrice, err := contractCaller.Client.SuggestGasPrice(context.Background())
	if err != nil {
		return err
	}

	auth.Value = big.NewInt(0)
	auth.GasLimit = contractCaller.GasLimit
	auth.GasPrice = gasPrice

	rsaReader := func() (*rsakey.RsaKey, error) {
		return contractCaller.Key.RsaKey, nil
	}
	err = h.setRsaKey(rsaReader)
	if err != nil {
		return err
	}

	h.lock.Lock()

	// assign
	h.contractCaller = contractCaller
	h.contractInstance = contractInstance
	h.contractTransactor = auth

	h.lock.Unlock()

	return nil
}

// UpdateSigners updates Handler's signers.
func (h *Handler) UpdateSigners(epochIdx uint64, signers []common.Address) error {
	h.lock.Lock()
	remoteSigners := h.signers
	h.lock.Unlock()

	for _, signer := range signers {
		if _, ok := remoteSigners[signer]; !ok {
			s := NewSigner(epochIdx, signer)
			remoteSigners[signer] = s
		}
	}

	h.lock.Lock()
	h.epochIdx = epochIdx
	h.signers = remoteSigners
	h.lock.Unlock()

	return nil
}

// DialAll connects remote signers.
func (h *Handler) DialAll() {
	h.lock.Lock()
	nodeID, address, contractInstance, auth, client := h.ownNodeID, h.ownAddress, h.contractInstance, h.contractTransactor, h.contractCaller.Client
	connected, signers, server := h.dialed, h.signers, h.server
	rsaKey := h.rsaKey
	h.lock.Unlock()

	if !connected {
		log.Debug("connecting...")

		for _, s := range signers {
			err := s.Dial(server, nodeID, address, auth, contractInstance, client, rsaKey)
			log.Debug("err when connect", "e", err)
		}
		connected = true
	}

	h.lock.Lock()
	h.dialed = connected
	h.lock.Unlock()

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

// BroadcastGeneratedBlock broadcasts generated block to committee
func (h *Handler) BroadcastGeneratedBlock(block *types.Block) {
	committee := h.signers
	log.Debug("broadcast new generated block to commttee")
	for addr, peer := range committee {
		log.Debug("signer", "addr", addr.Hex())
		peer.AsyncSendNewPendingBlock(block)
	}
}

// BroadcastPrepareSignedHeader broadcasts signed prepare header to remote committee
func (h *Handler) BroadcastPrepareSignedHeader(header *types.Header) {
	committee := h.signers
	for _, peer := range committee {
		peer.AsyncSendPrepareSignedHeader(header)
	}
}

// BroadcastCommitSignedHeader broadcasts signed commit header to remote committee
func (h *Handler) BroadcastCommitSignedHeader(header *types.Header) {
	committee := h.signers
	for _, peer := range committee {
		peer.AsyncSendCommitSignedHeader(header)
	}
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

func (h *Handler) handleMsg(p *Signer) error {
	log.Debug("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
	msg, err := p.rw.ReadMsg()
	if err != nil {
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

func (h *Handler) handle(version int, p *p2p.Peer, rw p2p.MsgReadWriter, address common.Address) error {
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
			return err
		}
	}
	// TODO: add defer to remove signer
	defer h.removeSigner(address)

	// main loop. handle incoming messages.
	for {
		if err := h.handleMsg(signer); err != nil {
			p.Log().Debug("Cpchain message handling failed", "err", err)
			return err
		}
	}
}

func (h *Handler) removeSigner(signer common.Address) error {

	if _, ok := h.signers[signer]; ok {
		delete(h.signers, signer)
	}

	return nil
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

			// select {
			// case <-h.quitSync:
			// 	return p2p.DiscQuitting
			// default:
			return h.handle(ProtocolVersion, p, rw, address)
			// }

		},
		NodeInfo: func() interface{} {
			return h.statusFn()
		},
		PeerInfo: func(id discover.NodeID) interface{} {
			return nil
		},
	}
}

// Start starts pbft handler
func (h *Handler) Start() {

	// Dail all remote signers
	go h.DialAll()

	// Broadcast mined pending block, including empty block
	go h.PendingBlockBroadcastLoop()

	return
}

// PendingBlockBroadcastLoop loops to broadcast blocks
func (h *Handler) PendingBlockBroadcastLoop() {
	futureTimer := time.NewTicker(10 * time.Second)
	defer futureTimer.Stop()

	for {
		select {
		case pendingBlock := <-h.pendingBlockCh:

			log.Debug("generated new pending block, broadcasting")

			// broadcast mined pending block to remote signers
			h.BroadcastGeneratedBlock(pendingBlock)

		// case <-futureTimer.C:

		// 	// check if still not received new block, if true, continue
		// 	if h.ReadyToImpeach() {

		// 		// get empty block
		// 		if emptyBlock, err := h.getEmptyBlockFn(); err == nil {

		// 			// broadcast the empty block
		// 			h.BroadcastGeneratedBlock(emptyBlock)
		// 		}
		// 	}

		case <-h.quitSync:
			return
		}
	}
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

// Stop stops all
func (h *Handler) Stop() {

	close(h.quitSync)

	return
}

// ReceiveMinedPendingBlock receives a block to add to pending block channel
func (h *Handler) ReceiveMinedPendingBlock(block *types.Block) error {
	select {
	case h.pendingBlockCh <- block:
		log.Debug("!!!!!!!!!!!!!!!!! inserted into handler.pendingBlockCh")
		return nil
	}
}

// SetFuncs sets some funcs
func (h *Handler) SetFuncs(
	validateSignerFn ValidateSignerFn,
	verifyHeaderFn VerifyHeaderFn,
	verifyBlockFn VerifyBlockFn,
	signHeaderFn SignHeaderFn,
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
	h.verifyBlockFn = verifyBlockFn
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

	return h.ownAddress
}

// SetSigner sets signer of handler
func (h *Handler) SetSigner(signer common.Address) {
	h.lock.Lock()
	defer h.lock.Unlock()

	if h.ownAddress != signer {
		h.ownAddress = signer
	}
}
