// Package dpor implements the dpor consensus engine.
package dpor

import (
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/hashicorp/golang-lru"
)

// BroadcastBlockFn broadcasts a block to normal peers(not pbft replicas)
type BroadcastBlockFn func(block *types.Block, prop bool)

const (
	inMemorySnapshots  = 100 // Number of recent vote snapshots to keep in memory
	inMemorySignatures = 100 // Number of recent block signatures to keep in memory

	pctA = 2
	pctB = 3 // only when n > 2/3 * N, accept the block
)

// Mode defines the type a dpor engine makes.
type Mode uint

const (
	NormalMode Mode = iota
	FakeMode
	DoNothingFakeMode
)

// Dpor is the proof-of-reputation consensus engine proposed to support the
// cpchain testnet.
type Dpor struct {
	dh     dporHelper
	db     database.Database   // Database to store and retrieve Snapshot checkpoints
	config *configs.DporConfig // Consensus engine configuration parameters

	recentSnaps *lru.ARCCache // Snapshots for recent block to speed up reorgs
	finalSigs   *lru.ARCCache // Final signatures of recent blocks to speed up mining
	prepareSigs *lru.ARCCache // The signatures of recent blocks for 'prepared' state

	signedBlocks     map[uint64]common.Hash // Record signed blocks.
	signedBlocksLock sync.RWMutex

	currentSnap     *DporSnapshot // Current snapshot
	currentSnapLock sync.RWMutex

	coinbase     common.Address // Coinbase of the miner(proposer or validator)
	signFn       backend.SignFn // Sign function to authorize hashes with
	coinbaseLock sync.RWMutex   // Protects the signer fields

	handler *backend.Handler

	isMiner     bool
	isMinerLock sync.RWMutex

	mode      Mode // used for test, always accept a block.
	fakeFail  uint64
	fakeDelay time.Duration // Time delay to sleep for before returning from verify
	modeLock  sync.RWMutex

	pbftState consensus.State
	stateLock sync.RWMutex

	client     backend.ClientBackend
	clientLock sync.RWMutex

	chain consensus.ChainReadWriter

	pmBroadcastBlockFn BroadcastBlockFn

	quitSync chan struct{}
}

// SignHash signs a hash msg with dpor coinbase account
func (d *Dpor) SignHash(hash []byte) ([]byte, error) {
	d.coinbaseLock.Lock()
	defer d.coinbaseLock.Unlock()

	var (
		coinbase = d.coinbase
		account  = accounts.Account{Address: coinbase}
	)

	return d.signFn(account, hash)
}

func (d *Dpor) IsMiner() bool {
	d.isMinerLock.RLock()
	defer d.isMinerLock.RUnlock()

	return d.isMiner
}

func (d *Dpor) SetAsMiner(isMiner bool) {
	d.isMinerLock.Lock()
	defer d.isMinerLock.Unlock()

	d.isMiner = isMiner
}

// Mode returns dpor mode
func (d *Dpor) Mode() Mode {
	d.modeLock.RLock()
	defer d.modeLock.RUnlock()

	return d.mode
}

// CurrentSnap returns current dpor snapshot
func (d *Dpor) CurrentSnap() *DporSnapshot {
	d.currentSnapLock.RLock()
	defer d.currentSnapLock.RUnlock()

	return d.currentSnap
}

// SetCurrentSnap sets current dpor snapshot
func (d *Dpor) SetCurrentSnap(snap *DporSnapshot) {
	d.currentSnapLock.Lock()
	defer d.currentSnapLock.Unlock()

	d.currentSnap = snap
}

func (d *Dpor) Client() backend.ClientBackend {
	d.clientLock.RLock()
	defer d.clientLock.RUnlock()

	return d.client
}

func (d *Dpor) SetClient(client backend.ClientBackend) {
	d.clientLock.Lock()
	defer d.clientLock.Unlock()

	d.client = client
}

// New creates a Dpor proof-of-reputation consensus engine with the initial
// signers set to the ones provided by the user.
func New(config *configs.DporConfig, db database.Database) *Dpor {

	// Set any missing consensus parameters to their defaults
	conf := *config
	if conf.TermLen == 0 {
		conf.TermLen = uint64(termLen)
	}
	if conf.ViewLen == 0 {
		conf.ViewLen = uint64(viewLen)
	}

	// Allocate the Snapshot caches and create the engine
	recentSnaps, _ := lru.NewARC(inMemorySnapshots)
	finalSigs, _ := lru.NewARC(inMemorySignatures)
	preparedSigs, _ := lru.NewARC(inMemorySignatures)

	signedBlocks := make(map[uint64]common.Hash)

	return &Dpor{
		dh:           &defaultDporHelper{&defaultDporUtil{}},
		config:       &conf,
		handler:      backend.NewHandler(&conf, common.Address{}),
		db:           db,
		recentSnaps:  recentSnaps,
		finalSigs:    finalSigs,
		prepareSigs:  preparedSigs,
		signedBlocks: signedBlocks,
	}
}

func NewFaker(config *configs.DporConfig, db database.Database) *Dpor {
	d := New(config, db)
	d.mode = FakeMode
	return d
}

func NewDoNothingFaker(config *configs.DporConfig, db database.Database) *Dpor {
	d := New(config, db)
	d.mode = DoNothingFakeMode
	return d
}

func NewFakeFailer(config *configs.DporConfig, db database.Database, fail uint64) *Dpor {
	d := NewDoNothingFaker(config, db)
	d.fakeFail = fail
	return d
}

func NewFakeDelayer(config *configs.DporConfig, db database.Database, delay time.Duration) *Dpor {
	d := NewFaker(config, db)
	d.fakeDelay = delay
	return d
}

// SetHandler sets dpor.handler
func (d *Dpor) SetHandler(handler *backend.Handler) error {
	d.handler = handler
	return nil
}

// IfSigned returns if already signed the block
func (d *Dpor) IfSigned(number uint64) (common.Hash, bool) {
	d.signedBlocksLock.RLock()
	defer d.signedBlocksLock.RUnlock()

	if hash, ok := d.signedBlocks[number]; ok {
		return hash, true
	}
	return common.Hash{}, false
}

// StartMining starts to create a handler and start it.
func (d *Dpor) StartMining(blockchain consensus.ChainReadWriter, server *p2p.Server, pmBroadcastBlockFn BroadcastBlockFn) {

	d.chain = blockchain

	d.pmBroadcastBlockFn = pmBroadcastBlockFn

	// TODO: @liq read f from config
	fsm := backend.NewDporStateMachine(d, 1)

	handler := d.handler

	if err := handler.SetServer(server); err != nil {
		return
	}

	if err := handler.SetDporService(d); err != nil {
		return
	}

	if err := handler.SetDporStateMachine(fsm); err != nil {
		return
	}

	handler.SetAvailable()

	d.handler = handler

	log.Debug("set dpor handler available!")

	var (
		header = d.chain.CurrentHeader()
		hash   = header.Hash()
		number = header.Number.Uint64()
	)

	snap, _ := d.dh.snapshot(d, d.chain, number, hash, nil)
	d.SetCurrentSnap(snap)

	go d.handler.Start()

	return
}

// StopMining stops dpor engine
func (d *Dpor) StopMining() {

	d.handler.Stop()
	return
}

// Coinbase returns current coinbase
func (d *Dpor) Coinbase() common.Address {
	d.coinbaseLock.RLock()
	defer d.coinbaseLock.RUnlock()

	return d.coinbase
}

// Protocol returns Dpor p2p protocol
func (d *Dpor) Protocol() consensus.Protocol {
	return d.handler.GetProtocol()
}

// PbftStatus returns current state of dpor
func (d *Dpor) PbftStatus() *consensus.PbftStatus {
	state := d.State()
	head := d.chain.CurrentHeader()
	return &consensus.PbftStatus{
		State: state,
		Head:  head,
	}
}

// HandleMinedBlock receives a block to add to handler's pending block channel
func (d *Dpor) HandleMinedBlock(block *types.Block) error {

	return d.handler.ReceiveMinedPendingBlock(block)
}

// ImpeachTimeout returns impeach time out
func (d *Dpor) ImpeachTimeout() time.Duration {
	return d.config.ImpeachTimeout
}
