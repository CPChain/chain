package backend

import (
	"errors"
	"sync"
	"time"

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
	dpor   DporService

	knownBlocks    *RecentBlocks
	pendingBlockCh chan *types.Block
	quitSync       chan struct{}

	lock sync.RWMutex
}

// NewHandler creates a new Handler
func NewHandler(config *configs.DporConfig, etherbase common.Address) *Handler {

	vh := &Handler{
		config:         config,
		coinbase:       etherbase,
		knownBlocks:    newKnownBlocks(),
		dialer:         newDialer(etherbase),
		pendingBlockCh: make(chan *types.Block),
		quitSync:       make(chan struct{}),
		available:      false,
	}

	// TODO: fix this
	vh.mode = LBFTMode

	return vh
}

// Start starts pbft handler
func (vh *Handler) Start() {

	if vh.isValidator {
		go vh.dialLoop()
	}

	// Broadcast mined pending block, including empty block
	go vh.PendingBlockBroadcastLoop()
	return
}

// Stop stops all
func (vh *Handler) Stop() {

	close(vh.quitSync)

	return
}

// GetProtocol returns handler protocol
func (vh *Handler) GetProtocol() consensus.Protocol {
	return vh
}

// NodeInfo returns node status
func (vh *Handler) NodeInfo() interface{} {

	return vh.dpor.Status()
}

// Name returns protocol name
func (vh *Handler) Name() string {
	return ProtocolName
}

// Version returns protocol version
func (vh *Handler) Version() uint {
	return ProtocolVersion
}

// Length returns protocol max msg code
func (vh *Handler) Length() uint64 {
	return ProtocolLength
}

// Available returns if handler is available
func (vh *Handler) Available() bool {
	vh.lock.RLock()
	defer vh.lock.RUnlock()

	return vh.available
}

// AddPeer adds a p2p peer to local peer set
func (vh *Handler) AddPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter) (string, bool, error) {
	coinbase := vh.Coinbase()
	verifyFn := vh.dpor.VerifyValidatorOf

	term := vh.dpor.FutureTermOf(vh.dpor.GetCurrentBlock().NumberU64())
	return vh.dialer.AddPeer(version, p, rw, coinbase, term, verifyFn)
}

// RemovePeer removes a p2p peer with its addr
func (vh *Handler) RemovePeer(addr string) error {
	return vh.dialer.removeRemoteProposers(addr)
}

// HandleMsg handles a msg of peer with id "addr"
func (vh *Handler) HandleMsg(addr string, msg p2p.Msg) error {

	remoteValidator, ok := vh.dialer.getValidator(addr)
	if !ok {
		// TODO: return new err
		return nil
	}

	return vh.handleMsg(remoteValidator, msg)
}

func (vh *Handler) handleMsg(p *RemoteValidator, msg p2p.Msg) error {
	log.Debug("handling msg", "msg", msg.Code)

	if msg.Code == NewValidatorMsg {
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

func (vh *Handler) SetContractCaller(contractCaller *ContractCaller) error {
	return vh.dialer.SetContractCaller(contractCaller)
}

func (vh *Handler) SetServer(server *p2p.Server) error {
	return vh.dialer.SetServer(server)
}

// SetDporService sets dpor service to handler
func (vh *Handler) SetDporService(dpor DporService) error {
	vh.dpor = dpor
	return nil
}

// Coinbase returns handler.signer
func (vh *Handler) Coinbase() common.Address {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	return vh.coinbase
}

// SetCoinbase sets coinbase of handler
func (vh *Handler) SetCoinbase(coinbase common.Address) {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	if vh.coinbase != coinbase {
		vh.coinbase = coinbase
	}
}

// IsAvailable returns if handler is available
func (vh *Handler) IsAvailable() bool {
	vh.lock.RLock()
	defer vh.lock.RUnlock()

	return vh.available
}

// SetAvailable sets available
func (vh *Handler) SetAvailable() {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	vh.available = true
}

// // GetPendingBlock returns a pending block with given hash
// func (vh *Handler) GetPendingBlock(number uint64) (*KnownBlock, error) {
// 	vh.lock.Lock()
// 	defer vh.lock.Unlock()

// 	block, err := vh.knownBlocks.GetKnownBlock(number)

// 	if err != nil {
// 		log.Debug("failed to get pending blocks", "number", number)
// 	}

// 	// log.Debug("got pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

// 	return block, err
// }

// // AddPendingBlock adds a pending block with given hash
// func (vh *Handler) AddPendingBlock(block *types.Block) error {
// 	vh.lock.Lock()
// 	defer vh.lock.Unlock()

// 	log.Debug("adding block to pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

// 	err := vh.knownBlocks.AddBlock(block)
// 	return err
// }

// // UpdateBlockStatus updates known block status
// func (vh *Handler) UpdateBlockStatus(number uint64, status BlockStatus) error {
// 	vh.lock.Lock()
// 	defer vh.lock.Unlock()

// 	log.Debug("updating block status", "number", number, "status", status)

// 	return vh.knownBlocks.UpdateStatus(number, status)
// }

func (vh *Handler) UpdateRemoteValidators(term uint64, validators []common.Address) error {
	return vh.dialer.UpdateRemoteValidators(term, validators)
}

func (vh *Handler) UploadEncryptedNodeInfo(term uint64) error {
	return vh.dialer.UploadEncryptedNodeInfo(term)
}

func (vh *Handler) dialLoop() {

	futureTimer := time.NewTicker(1 * time.Second)
	defer futureTimer.Stop()

	var block *types.Block

	for {
		select {
		case <-futureTimer.C:
			blk := vh.dpor.GetCurrentBlock()
			if block != nil {
				if blk.Number().Cmp(block.Number()) > 0 {
					// if there is an updated block, try to dial future proposers
					number := blk.NumberU64()
					go vh.dialer.DialAllRemoteProposers(number)
				}
			} else {
				block = blk
			}

		case <-vh.quitSync:
			return
		}
	}
}
