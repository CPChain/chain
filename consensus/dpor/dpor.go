// Package dpor implements the dpor consensus engine.
package dpor

import (
	"sync"
	"sync/atomic"
	"time"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/admission"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	lru "github.com/hashicorp/golang-lru"
)

// BroadcastBlockFn broadcasts a block to normal peers(not pbft replicas)
type BroadcastBlockFn func(block *types.Block, prop bool)

// SyncFromPeerFn tries to sync blocks from given peer
type SyncFromPeerFn func(p *p2p.Peer)

// SyncFromBestPeerFn tries to sync blocks from best peer
type SyncFromBestPeerFn func()

const (
	inMemorySnapshots  = 100 // Number of recent vote snapshots to keep in memory
	inMemorySignatures = 100 // Number of recent block signatures to keep in memory
)

// Mode defines the type a dpor engine makes.
type Mode uint

// DporMode
const (
	NormalMode Mode = iota
	FakeMode
	DoNothingFakeMode
	PbftFakeMode
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

	signedBlocks *signedBlocksRecord // Record signed blocks.

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
	ac         admission.ApiBackend
	clientLock sync.RWMutex

	chain consensus.ChainReadWriter

	pmBroadcastBlockFn   BroadcastBlockFn
	pmSyncFromPeerFn     SyncFromPeerFn
	pmSyncFromBestPeerFn SyncFromBestPeerFn

	quitSync chan struct{}

	lastCampaignTerm uint64 // the last term which the node has participated in campaign
	isToCampaign     int32  // indicate whether or not participate campaign, only elected proposer node can do mining
	// indicate whether the miner is running, there is a case that the dpor is running mining while campaign is stop,
	// it is by design and actually it does not generate any block in this case.
	runningMiner int32
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

// IsMiner returns if local coinbase is a miner(proposer or validator)
func (d *Dpor) IsMiner() bool {
	d.isMinerLock.RLock()
	defer d.isMinerLock.RUnlock()

	return d.isMiner
}

// SetAsMiner sets local coinbase as a miner
func (d *Dpor) SetAsMiner(isMiner bool) {
	d.isMinerLock.Lock()
	defer d.isMinerLock.Unlock()

	d.isMiner = isMiner
}

// IsToCampaign returns if it is time to campaign
func (d *Dpor) IsToCampaign() bool {
	return atomic.LoadInt32(&d.isToCampaign) > 0
}

// SetToCampaign sets isToCampaign as true
func (d *Dpor) SetToCampaign(isToCampaign bool) {
	if isToCampaign {
		atomic.StoreInt32(&d.isToCampaign, 1)
	} else {
		atomic.StoreInt32(&d.isToCampaign, 0)
	}
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

// Client returns a client backend to do contract related calls
func (d *Dpor) Client() backend.ClientBackend {
	d.clientLock.RLock()
	defer d.clientLock.RUnlock()

	return d.client
}

// SetClient sets given client as local client
func (d *Dpor) SetClient(client backend.ClientBackend) {
	d.clientLock.Lock()
	defer d.clientLock.Unlock()

	d.client = client
}

// New creates a Dpor proof-of-reputation consensus engine with the initial
// signers set to the ones provided by the user.
func New(config *configs.DporConfig, db database.Database, acBackend admission.ApiBackend) *Dpor {

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

	signedBlocks := newSignedBlocksRecord(db)

	return &Dpor{
		dh:           &defaultDporHelper{&defaultDporUtil{}},
		config:       &conf,
		handler:      backend.NewHandler(&conf, common.Address{}, db),
		ac:           acBackend,
		db:           db,
		recentSnaps:  recentSnaps,
		finalSigs:    finalSigs,
		prepareSigs:  preparedSigs,
		signedBlocks: signedBlocks,
	}
}

// NewFaker creates a new fake dpor
func NewFaker(config *configs.DporConfig, db database.Database) *Dpor {
	d := New(config, db, nil)
	d.mode = FakeMode
	return d
}

// NewDoNothingFaker creates a new fake dpor, do nothing when verifying blocks
func NewDoNothingFaker(config *configs.DporConfig, db database.Database) *Dpor {
	d := New(config, db, nil)
	d.mode = DoNothingFakeMode
	return d
}

// NewFakeFailer creates a new fake dpor, always fails when verifying blocks
func NewFakeFailer(config *configs.DporConfig, db database.Database, fail uint64) *Dpor {
	d := NewDoNothingFaker(config, db)
	d.fakeFail = fail
	return d
}

// NewFakeDelayer creates a new fake dpor, delays when verifying blocks
func NewFakeDelayer(config *configs.DporConfig, db database.Database, delay time.Duration) *Dpor {
	d := NewFaker(config, db)
	d.fakeDelay = delay
	return d
}

// NewPbftFaker creates a new fake dpor to work with pbft, not in use now
func NewPbftFaker(config *configs.DporConfig, db database.Database) *Dpor {
	d := New(config, db, nil)
	d.mode = PbftFakeMode
	return d
}

// SetHandler sets dpor.handler
func (d *Dpor) SetHandler(handler *backend.Handler) error {
	d.handler = handler
	return nil
}

// IfSigned checks if already signed a block
func (d *Dpor) IfSigned(number uint64) (common.Hash, bool) {
	return d.signedBlocks.ifAlreadySigned(number)
}

// MarkAsSigned marks signed a hash as signed
func (d *Dpor) MarkAsSigned(number uint64, hash common.Hash) error {
	return d.signedBlocks.markAsSigned(number, hash)
}

// SetChain is called by test file to assign the value of Dpor.chain, as well as DPor.currentSnapshot
func (d *Dpor) SetChain(blockchain consensus.ChainReadWriter) {
	d.chain = blockchain

	header := d.chain.CurrentHeader()
	number := header.Number.Uint64()
	hash := header.Hash()

	snap, _ := d.dh.snapshot(d, d.chain, number, hash, nil)
	d.SetCurrentSnap(snap)
}

// StartMining starts to create a handler and start it.
func (d *Dpor) StartMining(blockchain consensus.ChainReadWriter, server *p2p.Server, pmBroadcastBlockFn BroadcastBlockFn, pmSyncFromPeerFn SyncFromPeerFn, pmSyncFromBestPeerFn SyncFromBestPeerFn) {
	running := atomic.LoadInt32(&d.runningMiner) > 0
	// avoid launch handler twice
	if running {
		return
	}
	atomic.StoreInt32(&d.runningMiner, 1)

	d.chain = blockchain

	d.pmBroadcastBlockFn = pmBroadcastBlockFn
	d.pmSyncFromPeerFn = pmSyncFromPeerFn
	d.pmSyncFromBestPeerFn = pmSyncFromBestPeerFn

	var (
		faulty  = d.config.FaultyNumber
		handler = d.handler
	)

	fsm := backend.NewLBFT2(faulty, d, handler.ReceiveImpeachPendingBlock, d.db)

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
	running := atomic.LoadInt32(&d.runningMiner) > 0
	// avoid close twice
	if !running {
		return
	}
	atomic.StoreInt32(&d.runningMiner, 0)

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
