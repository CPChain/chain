// Package dpor implements the dpor consensus engine.
package dpor

import (
	"sync"
	"time"

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

type BroadcastBlockFn func(block *types.Block, prop bool)

const (
	inmemorySnapshots  = 50  // Number of recent vote snapshots to keep in memory
	inmemorySignatures = 100 // Number of recent block signatures to keep in memory

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

	recents     *lru.ARCCache // Snapshots for recent block to speed up reorgs
	finalSigs   *lru.ARCCache // Final signatures of recent blocks to speed up mining
	prepareSigs *lru.ARCCache // The signatures of recent blocks for 'prepared' state

	signedBlocks map[uint64]common.Hash // record signed blocks.

	currentSnapshot *DporSnapshot

	proposer common.Address // Cpchain address of the proposer
	signer   common.Address // signer is the validator
	signFn   SignFn         // Sign function to authorize hashes with

	// TODO: add proposerHandler here @shiyc

	validatorHandler *backend.Handler

	fake           Mode // used for test, always accept a block.
	fakeFail       uint64
	fakeDelay      time.Duration // Time delay to sleep for before returning from verify
	contractCaller *backend.ContractCaller

	pbftState consensus.State

	chain consensus.ChainReadWriter

	pmBroadcastBlockFn BroadcastBlockFn
	quitSync           chan struct{}

	lock sync.RWMutex // Protects the signer fields
}

func (d *Dpor) Mode() Mode {
	return d.fake
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
	recents, _ := lru.NewARC(inmemorySnapshots)
	finalSigs, _ := lru.NewARC(inmemorySignatures)
	preparedSigs, _ := lru.NewARC(inmemorySignatures)

	signedBlocks := make(map[uint64]common.Hash)

	return &Dpor{
		dh:               &defaultDporHelper{&defaultDporUtil{}},
		config:           &conf,
		validatorHandler: backend.NewHandler(&conf, common.Address{}),
		db:               db,
		recents:          recents,
		finalSigs:        finalSigs,
		prepareSigs:      preparedSigs,
		signedBlocks:     signedBlocks,
	}
}

func NewFaker(config *configs.DporConfig, db database.Database) *Dpor {
	d := New(config, db)
	d.fake = FakeMode
	return d
}

func NewDoNothingFaker(config *configs.DporConfig, db database.Database) *Dpor {
	d := New(config, db)
	d.fake = DoNothingFakeMode
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

// SetContractCaller sets dpor.contractCaller
func (d *Dpor) SetContractCaller(contractCaller *backend.ContractCaller) error {
	d.lock.Lock()
	defer d.lock.Unlock()
	d.contractCaller = contractCaller
	return nil
}

// SetHandler sets dpor.handler
func (d *Dpor) SetHandler(handler *backend.Handler) error {
	d.lock.Lock()
	defer d.lock.Unlock()
	d.validatorHandler = handler
	return nil
}

// IfSigned returns if already signed the block
func (d *Dpor) IfSigned(header *types.Header) bool {
	d.lock.Lock()
	defer d.lock.Unlock()

	if _, ok := d.signedBlocks[header.Number.Uint64()]; ok {
		return true
	}
	return false
}

// StartMining starts to create a handler and start it.
func (d *Dpor) StartMining(blockchain consensus.ChainReadWriter, contractCaller *backend.ContractCaller, server *p2p.Server, pmBroadcastBlockFn BroadcastBlockFn) {

	d.chain = blockchain
	d.contractCaller = contractCaller
	d.pmBroadcastBlockFn = pmBroadcastBlockFn

	// TODO: @liq read f from config
	fsm := backend.NewDporSm(d, 1)

	// create a pbft handler
	handler := d.validatorHandler

	if err := handler.SetContractCaller(contractCaller); err != nil {
		return
	}

	if err := handler.SetServer(server); err != nil {
		return
	}

	if err := handler.SetDporService(d); err != nil {
		return
	}

	if err := handler.SetDporSm(fsm); err != nil {
		return
	}

	d.validatorHandler = handler

	log.Debug("set available!!!!!!!!!!!!!!!!!")
	d.validatorHandler.SetAvailable()

	header := d.chain.CurrentHeader()
	number := header.Number.Uint64()
	hash := header.Hash()

	d.currentSnapshot, _ = d.dh.snapshot(d, d.chain, number, hash, nil)

	go d.validatorHandler.Start()

	return
}

// Start starts dpor engine to handle different phrases
func (d *Dpor) Start() {
	log.Info("Dpor started")
	return
}

// Stop stops dpor engine
func (d *Dpor) Stop() {
	log.Info("Dpor stopped")
	return
}

func (d *Dpor) Signer() common.Address {
	d.lock.Lock()
	defer d.lock.Unlock()

	return d.signer
}

func (d *Dpor) Proposer() common.Address {
	d.lock.Lock()
	defer d.lock.Unlock()

	return d.proposer
}

// Protocol returns Dpor p2p protocol
func (d *Dpor) Protocol() consensus.Protocol {
	return d.validatorHandler.GetProtocol()
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
	return d.validatorHandler.ReceiveMinedPendingBlock(block)
}

func (d *Dpor) ImpeachTimeout() time.Duration {
	return d.config.ImpeachTimeout
}
