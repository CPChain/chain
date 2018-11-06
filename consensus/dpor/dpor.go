// Package dpor implements the dpor consensus engine.
package dpor

import (
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/ethdb"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	lru "github.com/hashicorp/golang-lru"
)

const (
	inmemorySnapshots  = 1000 // Number of recent vote snapshots to keep in memory
	inmemorySignatures = 1000 // Number of recent block signatures to keep in memory

	pctA = 2
	pctB = 3 // only when n > 2/3 * N, accept the block
)

// Mode defines the type and amount of PoW verification an ethash engine makes.
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
	db     ethdb.Database      // Database to store and retrieve Snapshot checkpoints
	config *configs.DporConfig // Consensus engine configuration parameters

	recents    *lru.ARCCache // Snapshots for recent block to speed up reorgs
	signatures *lru.ARCCache // Signatures of recent blocks to speed up mining

	signedBlocks map[uint64]common.Hash // record signed blocks.

	signer common.Address // Ethereum address of the signing key
	signFn SignerFn       // Signer function to authorize hashes with

	handler *backend.Handler

	fake           Mode // used for test, always accept a block.
	fakeFail       uint64
	fakeDelay      time.Duration // Time delay to sleep for before returning from verify
	contractCaller *backend.ContractCaller

	pbftState backend.State

	chain consensus.ChainReader

	quitSync chan struct{}

	lock sync.RWMutex // Protects the signer fields
}

// New creates a Dpor proof-of-reputation consensus engine with the initial
// signers set to the ones provided by the user.
func New(config *configs.DporConfig, db ethdb.Database) *Dpor {

	// Set any missing consensus parameters to their defaults
	conf := *config
	if conf.Epoch == 0 {
		conf.Epoch = uint64(epochLength)
	}
	if conf.View == 0 {
		conf.View = uint64(viewLength)
	}

	// Allocate the Snapshot caches and create the engine
	recents, _ := lru.NewARC(inmemorySnapshots)
	signatures, _ := lru.NewARC(inmemorySignatures)

	signedBlocks := make(map[uint64]common.Hash)

	return &Dpor{
		dh:           &defaultDporHelper{&defaultDporUtil{}},
		config:       &conf,
		db:           db,
		recents:      recents,
		signatures:   signatures,
		signedBlocks: signedBlocks,
	}
}

func NewFaker(config *configs.DporConfig, db ethdb.Database) *Dpor {
	d := New(config, db)
	d.fake = FakeMode
	return d
}

func NewDoNothingFaker(config *configs.DporConfig, db ethdb.Database) *Dpor {
	d := New(config, db)
	d.fake = DoNothingFakeMode
	return d
}

func NewFakeFailer(config *configs.DporConfig, db ethdb.Database, fail uint64) *Dpor {
	d := NewDoNothingFaker(config, db)
	d.fakeFail = fail
	return d
}

func NewFakeDelayer(config *configs.DporConfig, db ethdb.Database, delay time.Duration) *Dpor {
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
	d.handler = handler
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

// Start starts dpor engine to handle different phrases
func (d *Dpor) Start() error {
	return nil
}

// Stop stops dpor engine
func (d *Dpor) Stop() error {
	return nil
}

func (d *Dpor) Coinbase() common.Address {
	d.lock.Lock()
	defer d.lock.Unlock()

	return d.signer
}

// ValidateSigner validates if given address is future signer
func (d *Dpor) ValidateSigner(address common.Address) (bool, error) {
	number := d.chain.CurrentHeader().Number.Uint64()
	return d.IsFutureSigner(d.chain, address, number)
}

func (d *Dpor) Protocol() p2p.Protocol {
	return d.handler.Protocol()
}

// PbftStatus returns current state of dpor
func (d *Dpor) PbftStatus() *backend.PbftStatus {
	state := d.State()
	head := d.chain.CurrentHeader()
	return &PbftStatus{
		state: state,
		head:  head,
	}
}
