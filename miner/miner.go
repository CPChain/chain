// Copyright 2018 The cpchain authors
// Copyright 2014 The go-ethereum Authors

package miner

import (
	"fmt"
	"sync/atomic"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/state"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/protocols/cpc/syncer"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/event"
)

// Backend wraps all methods required for mining.
type Backend interface {
	AccountManager() *accounts.Manager
	BlockChain() *core.BlockChain
	TxPool() *core.TxPool
	ChainDb() database.Database
}

// Miner creates blocks.
type Miner struct {
	mux      *event.TypeMux
	eng      *engine
	coinbase common.Address
	isMining int32
	backend  Backend
	cons     consensus.Engine

	// atomic values
	canStart    int32 // can start indicates whether we can start the mining operation
	shouldStart int32 // should start indicates whether we should start after sync
}

func New(backend Backend, config *configs.ChainConfig, mux *event.TypeMux, cons consensus.Engine) *Miner {
	miner := &Miner{
		mux:      mux,
		eng:      newEngine(config, cons, common.Address{}, backend, mux),
		backend:  backend,
		cons:     cons,
		canStart: 1,
	}

	miner.Register(NewNativeWorker(backend.BlockChain(), cons))
	// we sync up to the latest chain head
	go miner.downloaderSync()

	return miner
}

// update keeps track of the downloader events. Please be aware that this is a one shot type of update loop.
// It's entered once and as soon as `Done` or `Failed` has been broadcasted the events are unregistered and
// the loop is exited. This to prevent a major security vuln where external parties can DOS you with blocks
// and halt your mining operation for as long as the DOS continues.
func (m *Miner) downloaderSync() {
	events := m.mux.Subscribe(syncer.StartEvent{}, syncer.DoneEvent{}, syncer.FailedEvent{})
out:
	for ev := range events.Chan() {
		switch ev.Data.(type) {
		case syncer.StartEvent:
			atomic.StoreInt32(&m.canStart, 0)
			// stop mining first, and resume mining later
			if m.IsMining() {
				m.Stop()
				atomic.StoreInt32(&m.shouldStart, 1)
				log.Info("Mining aborted due to sync")
			}
		case syncer.DoneEvent, syncer.FailedEvent:
			shouldStart := atomic.LoadInt32(&m.shouldStart) == 1

			atomic.StoreInt32(&m.canStart, 1)
			atomic.StoreInt32(&m.shouldStart, 0)
			// resume
			if shouldStart {
				m.Start(m.coinbase)
			}
			// unsubscribe. we're only interested in this event once
			events.Unsubscribe()
			// stop immediately and ignore all further pending events
			break out
		}
	}
}

func (m *Miner) Start(coinbase common.Address) {
	atomic.StoreInt32(&m.shouldStart, 1)
	m.SetCoinbase(coinbase)

	if atomic.LoadInt32(&m.canStart) == 0 {
		log.Info("Network syncing, will start miner afterwards")
		return
	}
	atomic.StoreInt32(&m.isMining, 1)

	log.Info("Starting mining operation")

	m.eng.start()
	m.eng.commitNewWork()
}

func (m *Miner) Stop() {
	m.eng.stop()
	atomic.StoreInt32(&m.isMining, 0)
	atomic.StoreInt32(&m.shouldStart, 0)
}

func (m *Miner) Register(agent Worker) {
	if m.IsMining() {
		agent.Start()
	}
	m.eng.register(agent)
}

func (m *Miner) Unregister(agent Worker) {
	m.eng.unregister(agent)
}

func (m *Miner) IsMining() bool {
	return atomic.LoadInt32(&m.isMining) > 0
}

func (m *Miner) SetExtra(extra []byte) error {
	if uint64(len(extra)) > configs.MaximumExtraDataSize {
		return fmt.Errorf("extra exceeds max length. %d > %v", len(extra), configs.MaximumExtraDataSize)
	}
	m.eng.setExtra(extra)
	return nil
}

// Pending returns the currently pending block and associated state.
func (m *Miner) Pending() (*types.Block, *state.StateDB) {
	return m.eng.pending()
}

// PendingBlock returns the currently pending block.
//
// Note, to access both the pending block and the pending state
// simultaneously, please use Pending(), as the pending state can
// change between multiple method calls
func (m *Miner) PendingBlock() *types.Block {
	return m.eng.pendingBlock()
}

func (m *Miner) SetCoinbase(addr common.Address) {
	m.coinbase = addr
	m.eng.setCoinbase(addr)
}
