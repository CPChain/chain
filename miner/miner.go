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
	"bitbucket.org/cpchain/chain/protocols/cpc/downloader"
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

// Miner creates blocks and searches for proof-of-work values.
type Miner struct {
	mux *event.TypeMux

	eng *engine

	coinbase common.Address
	isMining int32
	backend  Backend
	cons     consensus.Engine

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
	go miner.downloaderSync()

	return miner
}

// update keeps track of the downloader events. Please be aware that this is a one shot type of update loop.
// It's entered once and as soon as `Done` or `Failed` has been broadcasted the events are unregistered and
// the loop is exited. This to prevent a major security vuln where external parties can DOS you with blocks
// and halt your mining operation for as long as the DOS continues.
func (self *Miner) downloaderSync() {
	events := self.mux.Subscribe(downloader.StartEvent{}, downloader.DoneEvent{}, downloader.FailedEvent{})
out:
	for ev := range events.Chan() {
		switch ev.Data.(type) {
		case downloader.StartEvent:
			atomic.StoreInt32(&self.canStart, 0)
			// stop mining first, and resume mining later
			if self.IsMining() {
				self.Stop()
				atomic.StoreInt32(&self.shouldStart, 1)
				log.Info("Mining aborted due to sync")
			}
		case downloader.DoneEvent, downloader.FailedEvent:
			shouldStart := atomic.LoadInt32(&self.shouldStart) == 1

			atomic.StoreInt32(&self.canStart, 1)
			atomic.StoreInt32(&self.shouldStart, 0)
			// resume
			if shouldStart {
				self.Start(self.coinbase)
			}
			// unsubscribe. we're only interested in this event once
			events.Unsubscribe()
			// stop immediately and ignore all further pending events
			break out
		}
	}
}

func (self *Miner) Start(coinbase common.Address) {
	atomic.StoreInt32(&self.shouldStart, 1)
	self.SetCoinbase(coinbase)

	if atomic.LoadInt32(&self.canStart) == 0 {
		log.Info("Network syncing, will start miner afterwards")
		return
	}
	atomic.StoreInt32(&self.isMining, 1)

	log.Info("Starting mining operation")

	self.eng.start()
	self.eng.commitNewWork()
}

func (self *Miner) Stop() {
	self.eng.stop()
	atomic.StoreInt32(&self.isMining, 0)
	atomic.StoreInt32(&self.shouldStart, 0)
}

func (self *Miner) Register(agent Worker) {
	if self.IsMining() {
		agent.Start()
	}
	self.eng.register(agent)
}

func (self *Miner) Unregister(agent Worker) {
	self.eng.unregister(agent)
}

func (self *Miner) IsMining() bool {
	return atomic.LoadInt32(&self.isMining) > 0
}

func (self *Miner) SetExtra(extra []byte) error {
	if uint64(len(extra)) > configs.MaximumExtraDataSize {
		return fmt.Errorf("extra exceeds max length. %d > %v", len(extra), configs.MaximumExtraDataSize)
	}
	self.eng.setExtra(extra)
	return nil
}

// Pending returns the currently pending block and associated state.
func (self *Miner) Pending() (*types.Block, *state.StateDB) {
	return self.eng.pending()
}

// PendingBlock returns the currently pending block.
//
// Note, to access both the pending block and the pending state
// simultaneously, please use Pending(), as the pending state can
// change between multiple method calls
func (self *Miner) PendingBlock() *types.Block {
	return self.eng.pendingBlock()
}

func (self *Miner) SetCoinbase(addr common.Address) {
	self.coinbase = addr
	self.eng.setCoinbase(addr)
}
