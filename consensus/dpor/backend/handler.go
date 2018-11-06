package backend

import (
	"context"
	"math/big"
	"sync"

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
	connected bool
	epochIdx  uint64

	ownNodeID  string
	ownAddress common.Address

	server *p2p.Server
	rsaKey *rsakey.RsaKey

	contractAddress    common.Address
	contractCaller     *ContractCaller
	contractInstance   *contract.SignerConnectionRegister
	contractTransactor *bind.TransactOpts

	signers map[common.Address]*Signer

	stateFn          StateFn
	statusFn         StatusFn
	addPendingFn     AddPendingBlockFn
	getPendingFn     GetPendingBlockFn
	verifyHeaderFn   VerifyHeaderFn
	signHeaderFn     SignHeaderFn
	insertChainFn    InsertChainFn
	broadcastBlockFn BroadcastBlockFn
	validateSignerFn ValidateSignerFn

	wg sync.WaitGroup

	newPeerCh chan *p2p.Peer
	quitSync  chan struct{}

	available bool

	lock sync.RWMutex
}

// New creates a PbftHandler
func New(config *configs.DporConfig, etherbase common.Address) (*Handler, error) {
	h := &Handler{
		ownAddress:      etherbase,
		contractAddress: config.Contracts["signer"],
		signers:         make(map[common.Address]*Signer),
		connected:       false,
	}
	return h, nil
}

// IsAvailable returns if handler is available
func (h *Handler) IsAvailable() bool {
	h.lock.Lock()
	defer h.lock.Unlock()

	return h.available
}

// SetServer sets handler.server
func (h *Handler) SetServer(server *p2p.Server) error {
	h.lock.Lock()
	defer h.lock.Unlock()

	h.server = server
	h.ownNodeID = server.Self().String()

	return nil
}

// SetRsaKey sets handler.rsaKey
func (h *Handler) SetRsaKey(rsaReader RsaReader) error {
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
	connected, signers, server := h.connected, h.signers, h.server
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
	h.connected = connected
	h.lock.Unlock()

}

// Disconnect disconnects all.
func (h *Handler) Disconnect() {
	h.lock.Lock()
	connected, signers, server := h.connected, h.signers, h.server
	h.lock.Unlock()

	if connected {
		log.Debug("disconnecting...")

		for _, s := range signers {
			err := s.disconnect(server)
			log.Debug("err when disconnect", "e", err)
		}

		h.connected = false
	}

	h.lock.Lock()
	h.connected = connected
	h.lock.Unlock()
}

// Start starts pbft handler
func (h *Handler) Start() error {
	return nil
}

// Stop stops all
func (h *Handler) Stop() error {
	return nil
}

// SendMsg sends msg to signer with given addr
func (h *Handler) SendMsg(addr common.Address, msg interface{}) error {
	return nil
}

// BroadcastMsg broadcasts msg to all
func (h *Handler) BroadcastMsg(msg interface{}) error {
	return nil
}

// BroadcastGeneratedBlock broadcasts generated block to committee
func (h *Handler) BroadcastGeneratedBlock(block *types.Block) {
	committee := h.signers
	for _, peer := range committee {
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

func (h *Handler) handlePreprepareMsg(msg p2p.Msg, p *Signer) error {
	switch {
	case msg.Code == PrepreparePendingBlockMsg:
		var request *types.Block
		if err := msg.Decode(&request); err != nil {
			return errResp(ErrDecode, "%v: %v", msg, err)
		}
		request.ReceivedAt = msg.ReceivedAt
		request.ReceivedFrom = p

		// Verify the block
		// if correct, sign it and broadcast as Prepare msg
		header := request.RefHeader()
		h.addPendingFn(request)
		switch err := h.verifyHeaderFn(header, Preprepared); err {
		case nil:
			go h.broadcastBlockFn(request, true)
			go h.broadcastBlockFn(request, false)

		case consensus.ErrNotEnoughSigs:

			switch e := h.verifyHeaderFn(header, Preprepared); e {
			case nil:
				go h.BroadcastPrepareSignedHeader(header)

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

		var header *types.Header
		if err := msg.Decode(&header); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		// Verify the signed header
		// if correct, rebroadcast it as Commit msg
		switch err := h.verifyHeaderFn(header, Prepared); err {
		case nil:
			go h.BroadcastCommitSignedHeader(header)

		case consensus.ErrNotEnoughSigs:
			// if !pm.engine.IfSigned(header) {
			// 	switch e := pm.SignHeader(header); e {
			// 	case nil:
			// 		go pm.BroadcastPrepareSignedHeader(header)

			// 	default:
			// 		return e
			// 	}
			// }

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
		// if correct, broadcast it as NewBlockMsg
		var header *types.Header
		if err := msg.Decode(&header); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		switch err := h.verifyHeaderFn(header, Committed); err {
		case nil:
			// if commited, insert to chain, then broadcast the block

			if block := h.getPendingFn(header.Hash()); block != nil {

				block = block.WithSeal(header)

				if err := h.insertChainFn(block); err != nil {
					return err
				}

				go h.broadcastBlockFn(block, true)
				go h.broadcastBlockFn(block, false)
			}

		case consensus.ErrNotEnoughSigs:
			// if !pm.engine.IfSigned(header) {
			// 	switch e := pm.SignHeader(header); e {
			// 	case nil:
			// 		go pm.BroadcastPrepareSignedHeader(header)

			// 	default:
			// 		return e
			// 	}
			// }

		default:
		}

	default:
		log.Warn("receievd unwelcome msg in state Prepare", "msg code", msg.Code)
	}

	return nil
}

func (h *Handler) handleMsg(msg p2p.Msg, p *Signer) error {
	if msg.Code == NewSignerMsg {
		return errResp(ErrExtraStatusMsg, "uncontrolled new signer message")
	}

	switch h.stateFn() {
	case NewRound:
		// if leader, send mined block with preprepare msg, enter preprepared
		// if not leader, wait for a new preprepare block, verify basic field, enter preprepared
		// if timer expired, send new empty block, enter preprepared

		h.handlePreprepareMsg(msg, p)

	case Preprepared:

		// broadcast prepare msg

		// wait for enough(>2f+1, >2/3) prepare msg, if true, enter prepared
		h.handlePrepareMsg(msg, p)

	case Prepared:

		// broadcast commit msg

		// wait for enough commit msg, if true, enter committed
		h.handleCommitMsg(msg, p)

	case Committed:
		// insert block to chain, if succeed, enter finalcommitted

	case FinalCommitted:
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
		return nil
	}

	if signer.Peer == nil {
		err := signer.SetSigner(version, p, rw)
		if err != nil {
			return err
		}
	}
	// TODO: add defer to remove signer

	// main loop. handle incoming messages.
	// for {
	// 	if err := ch.handleMsg(p); err != nil {
	// 		p.Log().Debug("Cpchain message handling failed", "err", err)
	// 		return err
	// 	}
	// }
	return nil
}

// Protocol returns a p2p protocol to handle dpor msgs
func (h *Handler) Protocol() p2p.Protocol {
	return p2p.Protocol{
		Name:    ProtocolName,
		Version: ProtocolVersion,
		Length:  ProtocolLength,
		Run: func(p *p2p.Peer, rw p2p.MsgReadWriter) error {

			cb := h.ownAddress
			validator := h.validateSignerFn

			ok, address, err := Handshake(p, rw, cb, validator)
			if !ok || err != nil {
				return err
			}

			select {
			case h.newPeerCh <- p:
				h.wg.Add(1)
				defer h.wg.Done()
				return h.handle(ProtocolVersion, p, rw, address)
			case <-h.quitSync:
				return p2p.DiscQuitting
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
