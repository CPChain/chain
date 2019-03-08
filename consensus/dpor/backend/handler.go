package backend

import (
	"errors"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

const (
	maxPendingBlocks = 256
)

var (
	// ErrUnknownHandlerMode is returned if in an unknown mode
	ErrUnknownHandlerMode = errors.New("unknown dpor handler mode")

	// ErrFailToAddPendingBlock is returned if failed to add block to pending
	ErrFailToAddPendingBlock = errors.New("fail to add pending block")

	// ErrNotSigner is returned if i am not a signer when handshaking
	// with remote signer
	ErrNotSigner = errors.New("local peer is not in the PV committees")
)

// Handler implements PbftHandler
type Handler struct {
	mode   HandlerMode
	config *configs.DporConfig

	available   bool
	isProposer  bool
	isValidator bool

	coinbase common.Address

	dialer *Dialer
	snap   *consensus.PbftStatus
	fsm    ConsensusStateMachine
	lbft   *LBFT
	dpor   DporService

	knownBlocks           *RecentBlocks
	pendingBlockCh        chan *types.Block
	pendingImpeachBlockCh chan *types.Block
	quitCh                chan struct{}

	broadcastRecord   *broadcastRecord
	impeachmentRecord *impeachmentRecord

	lock sync.RWMutex
}

// NewHandler creates a new Handler
func NewHandler(config *configs.DporConfig, coinbase common.Address, db database.Database) *Handler {

	h := &Handler{
		config:                config,
		coinbase:              coinbase,
		knownBlocks:           NewRecentBlocks(db),
		dialer:                NewDialer(),
		pendingBlockCh:        make(chan *types.Block),
		pendingImpeachBlockCh: make(chan *types.Block),
		quitCh:                make(chan struct{}),
		available:             false,

		broadcastRecord:   newBroadcastRecord(),
		impeachmentRecord: newImpeachmentRecord(),
	}

	// h.mode = LBFTMode
	h.mode = LBFT2Mode

	return h
}

// dialLoop loops to dial remote validators
func (h *Handler) dialLoop() {

	futureTimer := time.NewTicker(1 * time.Second)
	defer futureTimer.Stop()

	for {
		select {
		case <-futureTimer.C:

			blk := h.dpor.GetCurrentBlock()
			if blk != nil {
				term := h.dpor.TermOf(blk.NumberU64())
				if len(h.dialer.ValidatorsOfTerm(term)) < int(h.config.TermLen-h.fsm.Faulty()-1) {
					h.dialer.DialAllRemoteValidators(term)
				}
			} else {
				h.dialer.DialAllRemoteValidators(0)
			}

		case <-h.quitCh:
			return
		}
	}
}

// Start starts handler
func (h *Handler) Start() {

	// always dial if there is not enough validators in peer set
	go h.dialer.DialAllRemoteValidators(0)
	// go h.dialLoop()

	// broadcast mined pending block
	go h.PendingBlockBroadcastLoop()

	// broadcast impeachment block
	go h.PendingImpeachBlockBroadcastLoop()

	return
}

// Stop stops all
func (h *Handler) Stop() {

	close(h.quitCh)
	h.quitCh = make(chan struct{})

	return
}

// GetProtocol returns handler protocol
func (h *Handler) GetProtocol() consensus.Protocol {
	return h
}

// NodeInfo returns node status
func (h *Handler) NodeInfo() interface{} {

	return h.dpor.Status()
}

// Name returns protocol name
func (h *Handler) Name() string {
	return ProtocolName
}

// Version returns protocol version
func (h *Handler) Version() uint {
	return ProtocolVersion
}

// Length returns protocol max msg code
func (h *Handler) Length() uint64 {
	return ProtocolLength
}

// AddPeer adds a p2p peer to local peer set
func (h *Handler) AddPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter) (string, bool, bool, error) {
	var term, futureTerm uint64
	blk := h.dpor.GetCurrentBlock()
	if blk != nil {
		term = h.dpor.TermOf(blk.NumberU64())
		futureTerm = h.dpor.FutureTermOf(h.dpor.GetCurrentBlock().NumberU64())
	} else {
		term, futureTerm = 0, 0
	}

	mac, sig, err := h.dpor.GetMac()
	if err != nil {
		return "", false, false, err
	}

	return h.dialer.AddPeer(version, p, rw, mac, sig, term, futureTerm)
}

// RemovePeer removes a p2p peer with its addr
func (h *Handler) RemovePeer(addr string) {

	log.Debug("removing dpor peer", "addr", addr)

	_ = h.dialer.removeRemoteProposers(addr)
	_ = h.dialer.removeRemoteValidators(addr)

}

// HandleMsg handles a msg of peer with id "addr"
func (h *Handler) HandleMsg(addr string, msg p2p.Msg) error {

	remoteValidator, isV := h.dialer.getValidator(addr)
	remoteProposer, isP := h.dialer.getProposer(addr)

	if isV {
		return h.handleMsg(remoteValidator.RemoteSigner, msg)
	} else if isP {
		return h.handleMsg(remoteProposer.RemoteSigner, msg)
	} else {
		// TODO: the remote proposer is not in current proposer list, fix this
		log.Debug("received msg from remote peer, neither proposer nor validator", "coinbase", addr, "msgcode", msg.Code)
	}
	return nil
}

func (h *Handler) handleMsg(p *RemoteSigner, msg p2p.Msg) error {
	if msg.Code == NewSignerMsg {
		return errResp(ErrExtraStatusMsg, "uncontrolled new signer message")
	}

	switch h.mode {
	case LBFTMode:
		return h.handleLBFTMsg(msg, p)
	case LBFT2Mode:
		return h.handleLBFT2Msg(msg, p)
	default:
		return ErrUnknownHandlerMode
	}
}

// SetServer sets dialer.server
func (h *Handler) SetServer(server *p2p.Server) error {
	return h.dialer.SetServer(server)
}

// SetDporService sets dpor service to handler
func (h *Handler) SetDporService(dpor DporService) error {
	h.dpor = dpor
	h.dialer.SetDporService(dpor)
	return nil
}

// SetDporStateMachine sets dpor state machine
func (h *Handler) SetDporStateMachine(fsm ConsensusStateMachine) error {
	h.fsm = fsm
	return nil
}

// Coinbase returns handler.signer
func (h *Handler) Coinbase() common.Address {
	h.lock.Lock()
	defer h.lock.Unlock()

	return h.coinbase
}

// SetCoinbase sets coinbase of handler
func (h *Handler) SetCoinbase(coinbase common.Address) {
	h.lock.Lock()
	defer h.lock.Unlock()

	if h.coinbase != coinbase {
		h.coinbase = coinbase
	}
}

// SetAvailable sets available
func (h *Handler) SetAvailable() {
	h.lock.Lock()
	defer h.lock.Unlock()

	h.available = true
}

// Available returns if handler is available
func (h *Handler) Available() bool {
	h.lock.RLock()
	defer h.lock.RUnlock()

	return h.available
}
