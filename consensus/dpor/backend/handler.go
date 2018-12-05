package backend

import (
	"errors"
	"sync"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
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

	// ErrNotSigner is returned if i am not a signer when handshaking
	// with remote signer
	ErrNotSigner = errors.New("i am not a signer")
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
	fsm    *DporSm
	dpor   DporService

	knownBlocks    *RecentBlocks
	pendingBlockCh chan *types.Block
	quitSync       chan struct{}

	lock sync.RWMutex
}

// NewHandler creates a new Handler
func NewHandler(config *configs.DporConfig, coinbase common.Address) *Handler {

	h := &Handler{
		config:         config,
		coinbase:       coinbase,
		knownBlocks:    newKnownBlocks(),
		dialer:         NewDialer(coinbase, config.Contracts[configs.ContractProposer]),
		pendingBlockCh: make(chan *types.Block),
		quitSync:       make(chan struct{}),
		available:      false,
	}

	// TODO: fix this
	h.mode = LBFTMode
	// h.mode = PBFTMode

	return h
}

// Start starts pbft handler
func (h *Handler) Start() {

	if h.isValidator {
		go h.dialLoop()
	}

	// broadcast mined pending block, including empty block
	go h.PendingBlockBroadcastLoop()
	return
}

// Stop stops all
func (h *Handler) Stop() {

	close(h.quitSync)

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

// Available returns if handler is available
func (h *Handler) Available() bool {
	h.lock.RLock()
	defer h.lock.RUnlock()

	return h.available
}

// AddPeer adds a p2p peer to local peer set
func (h *Handler) AddPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter) (string, bool, bool, error) {
	coinbase := h.Coinbase()
	term := h.dpor.TermOf(h.dpor.GetCurrentBlock().NumberU64())
	futureTerm := h.dpor.FutureTermOf(h.dpor.GetCurrentBlock().NumberU64())
	verifyProposerFn := h.dpor.VerifyProposerOf
	verifyValidatorFn := h.dpor.VerifyValidatorOf

	amProposer, amValidator, _ := VerifyFutureSigner(coinbase, term, futureTerm, verifyProposerFn, verifyValidatorFn)
	continueHandshake := amProposer || amValidator
	if !continueHandshake {
		return common.Address{}.Hex(), false, false, ErrNotSigner
	}

	return h.dialer.AddPeer(version, p, rw, coinbase, term, futureTerm, verifyProposerFn, verifyValidatorFn)
}

// RemovePeer removes a p2p peer with its addr
func (h *Handler) RemovePeer(addr string) error {
	_ = h.dialer.removeRemoteProposers(addr)
	_ = h.dialer.removeRemoteValidators(addr)

	return nil
}

// HandleMsg handles a msg of peer with id "addr"
func (h *Handler) HandleMsg(addr string, msg p2p.Msg) error {

	remoteValidator, ok := h.dialer.getValidator(addr)
	if !ok {
		// TODO: return new err
		return nil
	}

	return h.handleMsg(remoteValidator, msg)
}

func (h *Handler) handleMsg(p *RemoteValidator, msg p2p.Msg) error {
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

// SetContractCaller sets dialer.contractCaller
func (h *Handler) SetContractCaller(contractCaller *ContractCaller) error {
	return h.dialer.SetContractCaller(contractCaller)
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

// SetDporSm sets dpor state machine
func (h *Handler) SetDporSm(fsm *DporSm) error {
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
