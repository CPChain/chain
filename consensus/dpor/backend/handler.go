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

	lock sync.RWMutex
}

// New creates a PbftHandler
func New(config *configs.DporConfig, etherbase common.Address) (*Handler, error) {
	ch := &Handler{
		ownAddress:      etherbase,
		contractAddress: config.Contracts["signer"],
		signers:         make(map[common.Address]*Signer),
		connected:       false,
	}
	return ch, nil
}

// SetServer sets handler.server
func (ch *Handler) SetServer(server *p2p.Server) error {
	ch.lock.Lock()
	defer ch.lock.Unlock()

	ch.server = server
	ch.ownNodeID = server.Self().String()

	return nil
}

// SetRsaKey sets handler.rsaKey
func (ch *Handler) SetRsaKey(rsaReader RsaReader) error {
	ch.lock.Lock()
	defer ch.lock.Unlock()

	var err error
	ch.rsaKey, err = rsaReader()

	return err
}

// SetContractCaller sets handler.contractcaller.
func (ch *Handler) SetContractCaller(contractCaller *ContractCaller) error {

	// creates an contract instance
	contractInstance, err := contract.NewSignerConnectionRegister(ch.contractAddress, contractCaller.Client)
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

	ch.lock.Lock()

	// assign
	ch.contractCaller = contractCaller
	ch.contractInstance = contractInstance
	ch.contractTransactor = auth

	ch.lock.Unlock()

	return nil
}

// UpdateSigners updates Handler's signers.
func (ch *Handler) UpdateSigners(epochIdx uint64, signers []common.Address) error {
	ch.lock.Lock()
	remoteSigners := ch.signers
	ch.lock.Unlock()

	for _, signer := range signers {
		if _, ok := remoteSigners[signer]; !ok {
			s := NewSigner(epochIdx, signer)
			remoteSigners[signer] = s
		}
	}

	ch.lock.Lock()
	ch.epochIdx = epochIdx
	ch.signers = remoteSigners
	ch.lock.Unlock()

	return nil
}

// DialAll connects remote signers.
func (ch *Handler) DialAll() {
	ch.lock.Lock()
	nodeID, address, contractInstance, auth, client := ch.ownNodeID, ch.ownAddress, ch.contractInstance, ch.contractTransactor, ch.contractCaller.Client
	connected, signers, server := ch.connected, ch.signers, ch.server
	rsaKey := ch.rsaKey
	ch.lock.Unlock()

	if !connected {
		log.Debug("connecting...")

		for _, s := range signers {
			err := s.Dial(server, nodeID, address, auth, contractInstance, client, rsaKey)
			log.Debug("err when connect", "e", err)
		}
		connected = true
	}

	ch.lock.Lock()
	ch.connected = connected
	ch.lock.Unlock()

}

// Disconnect disconnects all.
func (ch *Handler) Disconnect() {
	ch.lock.Lock()
	connected, signers, server := ch.connected, ch.signers, ch.server
	ch.lock.Unlock()

	if connected {
		log.Debug("disconnecting...")

		for _, s := range signers {
			err := s.disconnect(server)
			log.Debug("err when disconnect", "e", err)
		}

		ch.connected = false
	}

	ch.lock.Lock()
	ch.connected = connected
	ch.lock.Unlock()
}

// Start starts pbft handler
func (ch *Handler) Start() error {
	return nil
}

// Stop stops all
func (ch *Handler) Stop() error {
	return nil
}

// SendMsg sends msg to signer with given addr
func (ch *Handler) SendMsg(addr common.Address, msg interface{}) error {
	return nil
}

// BroadcastMsg broadcasts msg to all
func (ch *Handler) BroadcastMsg(msg interface{}) error {
	return nil
}

// BroadcastGeneratedBlock broadcasts generated block to committee
func (ch *Handler) BroadcastGeneratedBlock(block *types.Block) {
	committee := ch.signers
	for _, peer := range committee {
		peer.AsyncSendNewPendingBlock(block)
	}
}

// BroadcastPrepareSignedHeader broadcasts signed prepare header to remote committee
func (ch *Handler) BroadcastPrepareSignedHeader(header *types.Header) {
	committee := ch.signers
	for _, peer := range committee {
		peer.AsyncSendPrepareSignedHeader(header)
	}
}

// BroadcastCommitSignedHeader broadcasts signed commit header to remote committee
func (ch *Handler) BroadcastCommitSignedHeader(header *types.Header) {
	committee := ch.signers
	for _, peer := range committee {
		peer.AsyncSendCommitSignedHeader(header)
	}
}

func (ch *Handler) handlePreprepareMsg(msg p2p.Msg, p *Signer) error {
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
		ch.addPendingFn(request)
		switch err := ch.verifyHeaderFn(header, Preprepared); err {
		case nil:
			go ch.broadcastBlockFn(request, true)
			go ch.broadcastBlockFn(request, false)

		case consensus.ErrNotEnoughSigs:

			switch e := ch.verifyHeaderFn(header, Preprepared); e {
			case nil:
				go ch.BroadcastPrepareSignedHeader(header)

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

func (ch *Handler) handlePrepareMsg(msg p2p.Msg, p *Signer) error {
	switch {
	case msg.Code == PrepareSignedHeaderMsg:

		var header *types.Header
		if err := msg.Decode(&header); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		// Verify the signed header
		// if correct, rebroadcast it as Commit msg
		switch err := ch.verifyHeaderFn(header, Prepared); err {
		case nil:
			go ch.BroadcastCommitSignedHeader(header)

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

func (ch *Handler) handleCommitMsg(msg p2p.Msg, p *Signer) error {
	switch {
	case msg.Code == CommitSignedHeaderMsg:

		// Verify the signed header
		// if correct, broadcast it as NewBlockMsg
		var header *types.Header
		if err := msg.Decode(&header); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		switch err := ch.verifyHeaderFn(header, Committed); err {
		case nil:
			// if commited, insert to chain, then broadcast the block

			if block := ch.getPendingFn(header.Hash()); block != nil {

				block = block.WithSeal(header)

				if err := ch.insertChainFn(block); err != nil {
					return err
				}

				go ch.broadcastBlockFn(block, true)
				go ch.broadcastBlockFn(block, false)
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

func (ch *Handler) handleMsg(msg p2p.Msg, p *Signer) error {
	if msg.Code == NewSignerMsg {
		return errResp(ErrExtraStatusMsg, "uncontrolled new signer message")
	}

	switch ch.stateFn() {
	case NewRound:
		// if leader, send mined block with preprepare msg, enter preprepared
		// if not leader, wait for a new preprepare block, verify basic field, enter preprepared
		// if timer expired, send new empty block, enter preprepared

		ch.handlePreprepareMsg(msg, p)

	case Preprepared:

		// broadcast prepare msg

		// wait for enough(>2f+1, >2/3) prepare msg, if true, enter prepared
		ch.handlePrepareMsg(msg, p)

	case Prepared:

		// broadcast commit msg

		// wait for enough commit msg, if true, enter committed
		ch.handleCommitMsg(msg, p)

	case Committed:
		// insert block to chain, if succeed, enter finalcommitted

	case FinalCommitted:
		// broadcast block to normal peers, once finished, enter newround

	default:
		return consensus.ErrUnknownPbftState
	}

	return nil
}

func (ch *Handler) handle(version int, p *p2p.Peer, rw p2p.MsgReadWriter, address common.Address) error {
	// TODO: add lock here
	signer, ok := ch.signers[address]

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
func (ch *Handler) Protocol() p2p.Protocol {
	return p2p.Protocol{
		Name:    ProtocolName,
		Version: ProtocolVersion,
		Length:  ProtocolLength,
		Run: func(p *p2p.Peer, rw p2p.MsgReadWriter) error {

			cb := ch.ownAddress
			validator := ch.validateSignerFn

			ok, address, err := Handshake(p, rw, cb, validator)
			if !ok || err != nil {
				return err
			}

			select {
			case ch.newPeerCh <- p:
				ch.wg.Add(1)
				defer ch.wg.Done()
				return ch.handle(ProtocolVersion, p, rw, address)
			case <-ch.quitSync:
				return p2p.DiscQuitting
			}

		},
		NodeInfo: func() interface{} {
			return ch.statusFn()
		},
		PeerInfo: func(id discover.NodeID) interface{} {
			return nil
		},
	}
}
