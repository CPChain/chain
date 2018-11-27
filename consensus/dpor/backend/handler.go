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

	remoteProposers  map[common.Address]*RemoteProposer
	remoteValidators map[common.Address]*RemoteValidator

	// previous stable pbft status
	snap *consensus.PbftStatus
	dpor DporService

	pendingBlockCh chan *types.Block
	quitSync       chan struct{}

	dialed    bool
	available bool

	lock sync.RWMutex
}

// NewHandler creates a new Handler
func NewHandler(config *configs.DporConfig, etherbase common.Address) *Handler {
	vh := &Handler{
		coinbase:         etherbase,
		contractAddress:  config.Contracts["signer"],
		termLen:          config.TermLen,
		maxInitNumber:    config.MaxInitBlockNumber,
		remoteValidators: make(map[common.Address]*RemoteValidator),
		knownBlocks:      NewKnownBlocks(),
		pendingBlockCh:   make(chan *types.Block),
		quitSync:         make(chan struct{}),
		dialed:           false,
		available:        false,
	}

	// TODO: fix this
	vh.mode = LBFTMode

	return vh
}

// Start starts pbft handler
func (vh *Handler) Start() {

	// Dail all remote validators
	// go vh.DialAllRemoteValidators()

	// TODO: dail all remote proposers

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
	validator := vh.dpor.VerifyRemoteValidator

	log.Debug("do handshaking with remote peer...")

	ok, address, err := ValidatorHandshake(p, rw, coinbase, validator)
	if !ok || err != nil {
		log.Debug("failed to handshake in dpor", "err", err, "ok", ok)
		return "", ok, err
	}
	remoteValidator, err := vh.addRemoteValidator(version, p, rw, address)

	log.Debug("after add remote validator", "validator", remoteValidator.ID(), "err", err)
	for addr, s := range vh.remoteValidators {
		log.Debug("validators in handler", "addr", addr.Hex(), "id", s.ID())
	}

	return address.Hex(), true, err
}

// RemovePeer removes a p2p peer with its addr
func (vh *Handler) RemovePeer(addr string) error {
	return vh.removeRemoteValidator(addr)
}

// HandleMsg handles a msg of peer with id "addr"
func (vh *Handler) HandleMsg(addr string, msg p2p.Msg) error {

	remoteValidator, ok := vh.remoteValidators[common.HexToAddress(addr)]
	if !ok {
		// TODO: return new err
		return nil
	}

	return vh.handleMsg(remoteValidator, msg)
}

func (vh *Handler) addRemoteValidator(version int, p *p2p.Peer, rw p2p.MsgReadWriter, address common.Address) (*RemoteValidator, error) {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	// TODO: add lock here
	remoteValidator, ok := vh.remoteValidators[address]

	if !ok {
		// TODO: @liuq fix this
		remoteValidator = NewRemoteValidator(vh.term, address)
	}

	log.Debug("adding remote validator...", "validator", address.Hex())

	err := remoteValidator.SetPeer(version, p, rw)
	if err != nil {
		log.Debug("failed to set remote validator")
		return nil, err
	}

	err = remoteValidator.AddStatic(vh.server)
	if err != nil {
		log.Debug("failed to add remote validator as static peer")
		return nil, err
	}

	go remoteValidator.broadcastLoop()

	vh.remoteValidators[address] = remoteValidator
	return remoteValidator, nil
}

func (vh *Handler) removeRemoteValidator(addr string) error {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	validatorAddr := common.HexToAddress(addr)

	if _, ok := vh.remoteValidators[validatorAddr]; ok {
		delete(vh.remoteValidators, validatorAddr)
	}

	return nil
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

// Disconnect disconnects all.
func (vh *Handler) Disconnect() {
	vh.lock.Lock()
	connected, remoteValidators, server := vh.dialed, vh.remoteValidators, vh.server
	vh.lock.Unlock()

	if connected {
		log.Debug("disconnecting...")

		for _, s := range remoteValidators {
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
func (vh *Handler) GetPendingBlock(number uint64) (*KnownBlock, error) {
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
func (vh *Handler) AddPendingBlock(block *types.Block) error {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	log.Debug("adding block to pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

	err := vh.knownBlocks.AddBlock(block)
	return err
}

// UpdateBlockStatus updates known block status
func (vh *Handler) UpdateBlockStatus(number uint64, status BlockStatus) error {
	vh.lock.Lock()
	defer vh.lock.Unlock()

	log.Debug("updating block status", "number", number, "status", status)

	return vh.knownBlocks.UpdateStatus(number, status)
}
