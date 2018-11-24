package miner

import (
	"math/big"
	"sync"
	"sync/atomic"
	"time"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/state"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/event"
)

const (
	resultQueueSize  = 10
	miningLogAtDepth = 5
	// txChanSize is the size of channel listening to NewTxsEvent.
	// The number is referenced from the size of tx pool.
	txChanSize = 4096
	// chainHeadChanSize is the size of channel listening to ChainHeadEvent.
	chainHeadChanSize = 10
	// chainSideChanSize is the size of channel listening to ChainSideEvent.
	chainSideChanSize = 10
)

// Worker can register itself with the engine
type Worker interface {
	// retrieve the channel to pass work to a worker
	Work() chan<- *Work
	// retrieve result from a worker
	SetReturnCh(chan<- *Result)
	Stop()
	Start()
}

// Work is the workers current environment and holds
// all of the current state information
type Work struct {
	config *configs.ChainConfig // manifest which chain we are on
	signer types.Signer         // the signer, e.g., cep1signer to recover the transaction sender

	privState *state.StateDB          // apply public state changes here
	pubState  *state.StateDB          // apply private state changes here
	remoteDB  database.RemoteDatabase // ipfs database used for private tx processing
	tcount    int                     // tx count in cycle
	gasPool   *core.GasPool           // available gas used to pack transactions

	Block *types.Block // the new block

	header       *types.Header
	txs          []*types.Transaction
	pubReceipts  []*types.Receipt
	privReceipts []*types.Receipt

	accm      *accounts.Manager
	createdAt time.Time
}

type Result struct {
	Work  *Work
	Block *types.Block
}

// engine is the main object which takes care of applying messages to the new state
type engine struct {
	mu sync.Mutex

	config *configs.ChainConfig
	cons   consensus.Engine

	// update loop
	mux          *event.TypeMux
	txsCh        chan core.NewTxsEvent // new transactions enter the transaction pool
	txsSub       event.Subscription
	chainHeadCh  chan core.ChainHeadEvent // a new block has been inserted into the chain
	chainHeadSub event.Subscription
	chainSideCh  chan core.ChainSideEvent // a side block has been inserted
	chainSideSub event.Subscription

	workers map[Worker]struct{} // set of workers
	recv    chan *Result        // the channel that receives the result from workers

	backend Backend  // cpchain service backend
	chain   *core.BlockChain  // pointer cuz we have only one canonical chain in the whole system
	proc    core.Validator
	chainDb database.Database

	coinbase common.Address
	extra    []byte

	currentMu   sync.Mutex
	currentWork *Work

	snapshotMu    sync.RWMutex
	snapshotBlock *types.Block
	snapshotState *state.StateDB

	unconfirmed *unconfirmedBlocks // set of locally mined blocks pending canonical confirmations

	// atomic status counters
	mining int32
	atWork int32
}

func newEngine(config *configs.ChainConfig, cons consensus.Engine, coinbase common.Address, backend Backend, mux *event.TypeMux) *engine {
	eng := &engine{
		config:      config,
		cons:        cons,
		backend:     backend,
		mux:         mux,
		txsCh:       make(chan core.NewTxsEvent, txChanSize),
		chainHeadCh: make(chan core.ChainHeadEvent, chainHeadChanSize),
		chainSideCh: make(chan core.ChainSideEvent, chainSideChanSize),
		chainDb:     backend.ChainDb(),
		recv:        make(chan *Result, resultQueueSize),
		chain:       backend.BlockChain(),
		proc:        backend.BlockChain().Validator(), // processor validator lock
		coinbase:    coinbase,
		workers:     make(map[Worker]struct{}),
		// we don't really need this.  but keep it here for more debugging information.
		unconfirmed: newUnconfirmedBlocks(backend.BlockChain(), miningLogAtDepth),
	}

	// Subscribe NewTxsEvent for tx pool
	eng.txsSub = backend.TxPool().SubscribeNewTxsEvent(eng.txsCh)
	// Subscribe events for blockchain
	eng.chainHeadSub = backend.BlockChain().SubscribeChainHeadEvent(eng.chainHeadCh)
	eng.chainSideSub = backend.BlockChain().SubscribeChainSideEvent(eng.chainSideCh)
	go eng.update()

	go eng.wait()
	eng.commitNewWork()

	return eng
}

func (self *engine) setCoinbase(addr common.Address) {
	self.mu.Lock()
	defer self.mu.Unlock()
	self.coinbase = addr
}

func (self *engine) setExtra(extra []byte) {
	self.mu.Lock()
	defer self.mu.Unlock()
	self.extra = extra
}

func (self *engine) pending() (*types.Block, *state.StateDB) {
	if atomic.LoadInt32(&self.mining) == 0 {
		// return a snapshot to avoid contention on currentMu mutex
		self.snapshotMu.RLock()
		defer self.snapshotMu.RUnlock()
		return self.snapshotBlock, self.snapshotState.Copy()
	}

	self.currentMu.Lock()
	defer self.currentMu.Unlock()
	return self.currentWork.Block, self.currentWork.pubState.Copy()
}

func (self *engine) pendingBlock() *types.Block {
	if atomic.LoadInt32(&self.mining) == 0 {
		// return a snapshot to avoid contention on currentMu mutex
		self.snapshotMu.RLock()
		defer self.snapshotMu.RUnlock()
		return self.snapshotBlock
	}

	self.currentMu.Lock()
	defer self.currentMu.Unlock()
	return self.currentWork.Block
}

func (self *engine) start() {
	self.mu.Lock()
	defer self.mu.Unlock()

	atomic.StoreInt32(&self.mining, 1)

	// spin up workers
	for worker := range self.workers {
		worker.Start()
	}
}

func (self *engine) stop() {
	self.mu.Lock()
	defer self.mu.Unlock()
	if atomic.LoadInt32(&self.mining) == 1 {
		for worker := range self.workers {
			worker.Stop()
		}
	}
	atomic.StoreInt32(&self.mining, 0)
	atomic.StoreInt32(&self.atWork, 0)
}

func (self *engine) register(worker Worker) {
	self.mu.Lock()
	defer self.mu.Unlock()
	self.workers[worker] = struct{}{}
	worker.SetReturnCh(self.recv)
}

func (self *engine) unregister(worker Worker) {
	self.mu.Lock()
	defer self.mu.Unlock()
	delete(self.workers, worker)
	worker.Stop()
}

func (self *engine) update() {
	defer self.txsSub.Unsubscribe()
	defer self.chainHeadSub.Unsubscribe()
	defer self.chainSideSub.Unsubscribe()

	for {
		// A real event arrived, process interesting content
		select {
		// Handle ChainHeadEvent
		case <-self.chainHeadCh:
			self.commitNewWork()

		// Handle ChainSideEvent
		case ev := <-self.chainSideCh:
			log.Warn("Got unexpected uncle block ", "hash", ev.Block.Hash().Hex())

		// Handle NewTxsEvent
		case ev := <-self.txsCh:
			// Apply transactions to the pending state if we're not mining.
			//
			// Note all transactions received may not be continuous with transactions
			// already included in the current mining block. These transactions will
			// be automatically eliminated.
			if atomic.LoadInt32(&self.mining) == 0 {
				self.currentMu.Lock()
				txs := make(map[common.Address]types.Transactions)
				for _, tx := range ev.Txs {
					acc, _ := types.Sender(self.currentWork.signer, tx)
					txs[acc] = append(txs[acc], tx)
				}
				txset := types.NewTransactionsByPriceAndNonce(self.currentWork.signer, txs)
				self.currentWork.commitTransactions(self.mux, txset, self.chain, self.coinbase)
				self.updateSnapshot()
				self.currentMu.Unlock()
			} else {
				// If we're mining, but nothing is being processed, wake on new transactions
				if self.config.Dpor != nil && self.config.Dpor.Period == 0 {
					self.commitNewWork()
				}
			}

		// System stopped
		case <-self.txsSub.Err():
			return
		case <-self.chainHeadSub.Err():
			return
		case <-self.chainSideSub.Err():
			return
		}
	}
}

func (self *engine) wait() {
	for {
		for result := range self.recv {
			atomic.AddInt32(&self.atWork, -1)

			if result == nil {
				continue
			}
			block := result.Block
			work := result.Work

			// Update the block hash in all logs since it is now available and not when the
			// receipt/log of individual transactions were created.
			for _, r := range append(work.pubReceipts, work.privReceipts...) {
				for _, l := range r.Logs {
					l.BlockHash = block.Hash()
				}
			}
			for _, log := range append(work.pubState.Logs(), work.privState.Logs()...) {
				log.BlockHash = block.Hash()
			}

			stat, err := self.chain.WriteBlockWithState(block, work.pubReceipts, work.privReceipts, work.pubState, work.privState)
			if err != nil {
				log.Error("Failed writing block to chain", "err", err)
				continue
			}

			// Broadcast the block and announce chain insertion event
			self.mux.Post(core.NewMinedBlockEvent{Block: block})
			var (
				events []interface{}
				// TODO: try merging private logs
				logs = work.pubState.Logs()
			)
			events = append(events, core.ChainEvent{Block: block, Hash: block.Hash(), Logs: logs})
			if stat == core.CanonStatTy {
				events = append(events, core.ChainHeadEvent{Block: block})
			}
			self.chain.PostChainEvents(events, logs)

			// Insert the block into the set of pending ones to wait for confirmations
			self.unconfirmed.Insert(block.NumberU64(), block.Hash())
		}
	}
}

// push sends a new work task to currently live miner workers.
func (self *engine) push(work *Work) {
	if atomic.LoadInt32(&self.mining) != 1 {
		return
	}
	for worker := range self.workers {
		atomic.AddInt32(&self.atWork, 1)
		if ch := worker.Work(); ch != nil {
			ch <- work
		}
	}
}

// makeCurrentWork creates a new environment for the current cycle.
func (self *engine) makeCurrentWork(parent *types.Block, header *types.Header) error {
	pubState, err := self.chain.StateAt(parent.StateRoot())
	if err != nil {
		return err
	}

	privState, err := self.chain.StatePrivAt(parent.StateRoot())
	if err != nil {
		return err
	}

	work := &Work{
		config:    self.config,
		signer:    types.NewCep1Signer(self.config.ChainID),
		pubState:  pubState,
		privState: privState,
		header:    header,
		createdAt: time.Now(),
		remoteDB:  self.chain.RemoteDB(),
		accm:      self.backend.AccountManager(),
	}

	// Keep track of transactions which return errors so they can be removed
	work.tcount = 0
	self.currentWork = work
	return nil
}

// commitNewWork creates a new block.
func (self *engine) commitNewWork() {
	self.mu.Lock()
	defer self.mu.Unlock()
	self.currentMu.Lock()
	defer self.currentMu.Unlock()

	tstart := time.Now()
	parent := self.chain.CurrentBlock()

	tstamp := tstart.Unix()
	if parent.Time().Cmp(new(big.Int).SetInt64(tstamp)) >= 0 {
		tstamp = parent.Time().Int64() + 1
	}
	// this will ensure we're not going off too far in the future
	if now := time.Now().Unix(); tstamp > now+1 {
		wait := time.Duration(tstamp-now) * time.Second
		log.Info("Mining too far in the future", "wait", common.PrettyDuration(wait))
		time.Sleep(wait)
	}

	num := parent.Number()
	header := &types.Header{
		ParentHash: parent.Hash(),
		Number:     num.Add(num, common.Big1),
		GasLimit:   core.CalcGasLimit(parent),
		Extra:      self.extra,
		Time:       big.NewInt(tstamp),
	}
	// Only set the coinbase if we are mining (avoid spurious block rewards)
	if atomic.LoadInt32(&self.mining) == 1 {
		header.Coinbase = self.coinbase
	}
	if err := self.cons.PrepareBlock(self.chain, header); err != nil {
		log.Error("Failed to prepare header for mining", "err", err)
		return
	}

	// Could potentially happen if starting to mine in an odd state.
	err := self.makeCurrentWork(parent, header)
	if err != nil {
		log.Error("Failed to create mining context", "err", err)
		return
	}
	// Create the current work task and check any fork transitions needed
	work := self.currentWork
	pending, err := self.backend.TxPool().Pending()
	if err != nil {
		log.Error("Failed to fetch pending transactions", "err", err)
		return
	}
	txs := types.NewTransactionsByPriceAndNonce(self.currentWork.signer, pending)
	work.commitTransactions(self.mux, txs, self.chain, self.coinbase)

	// TODO @jason please give a more unified api to access the signer
	header.Coinbase = self.cons.(*dpor.Dpor).Proposer()

	// Create the new block to seal with the consensus engine. Private tx's receipts are not involved computing block's
	// receipts hash and receipts bloom as they are private and not guaranteeing identical in different nodes.
	if work.Block, err = self.cons.Finalize(self.chain, header, work.pubState, work.txs, []*types.Header{}, work.pubReceipts); err != nil {
		log.Error("Failed to finalize block for sealing", "err", err)
		return
	}

	// We only care about logging if we're actually mining.
	if atomic.LoadInt32(&self.mining) == 1 {
		log.Info("Commit new mining work", "number", work.Block.Number(), "txs", work.tcount, "elapsed", common.PrettyDuration(time.Since(tstart)))
		self.unconfirmed.Shift(work.Block.NumberU64() - 1)
	}
	self.push(work)
	self.updateSnapshot()
}

func (self *engine) updateSnapshot() {
	self.snapshotMu.Lock()
	defer self.snapshotMu.Unlock()

	self.snapshotBlock = types.NewBlock(
		self.currentWork.header,
		self.currentWork.txs,
		self.currentWork.pubReceipts,
	)
	self.snapshotState = self.currentWork.pubState.Copy()
	// TODO: if need to snapshot private state?
}

func (env *Work) commitTransactions(mux *event.TypeMux, txs *types.TransactionsByPriceAndNonce, bc *core.BlockChain, coinbase common.Address) {
	if env.gasPool == nil {
		env.gasPool = new(core.GasPool).AddGas(env.header.GasLimit)
	}

	var coalescedLogs []*types.Log

	for {
		// If we don't have enough gas for any further transactions then we're done
		if env.gasPool.Gas() < configs.TxGas {
			log.Debug("Not enough gas for further transactions", "have", env.gasPool, "want", configs.TxGas)
			break
		}
		// Retrieve the next transaction and abort if all done
		tx := txs.Peek()
		if tx == nil {
			break
		}
		// Error may be ignored here. The error has already been checked
		// during transaction acceptance is the transaction pool.
		//
		// We use the eip155 signer regardless of the current hf.
		from, _ := types.Sender(env.signer, tx)

		// Start executing the transaction
		env.pubState.Prepare(tx.Hash(), common.Hash{}, env.tcount)
		env.privState.Prepare(tx.Hash(), common.Hash{}, env.tcount)

		err, logs := env.commitTransaction(tx, bc, coinbase, env.gasPool)
		switch err {
		case core.ErrGasLimitReached:
			// Pop the current out-of-gas transaction without shifting in the next from the account
			log.Debug("Gas limit exceeded for current block", "sender", from)
			txs.Pop()

		case core.ErrNonceTooLow:
			// New head notification data race between the transaction pool and miner, shift
			log.Debug("Skipping transaction with low nonce", "sender", from, "nonce", tx.Nonce())
			txs.Shift()

		case core.ErrNonceTooHigh:
			// Reorg notification data race between the transaction pool and miner, skip account =
			log.Debug("Skipping account with hight nonce", "sender", from, "nonce", tx.Nonce())
			txs.Pop()

		case nil:
			// Everything ok, collect the logs and shift in the next transaction from the same account
			coalescedLogs = append(coalescedLogs, logs...)
			env.tcount++
			txs.Shift()

		default:
			// Strange error, discard the transaction and get the next in line (note, the
			// nonce-too-high clause will prevent us from executing in vain).
			log.Debug("Transaction failed, account skipped", "hash", tx.Hash(), "err", err)
			txs.Shift()
		}
	}

	if len(coalescedLogs) > 0 || env.tcount > 0 {
		// make a copy, the state caches the logs and these logs get "upgraded" from pending to mined
		// logs by filling in the block hash when the block was mined by the local miner. This can
		// cause a race condition if a log was "upgraded" before the PendingLogsEvent is processed.
		cpy := make([]*types.Log, len(coalescedLogs))
		for i, l := range coalescedLogs {
			cpy[i] = new(types.Log)
			*cpy[i] = *l
		}
		go func(logs []*types.Log, tcount int) {
			if len(logs) > 0 {
				mux.Post(core.PendingLogsEvent{Logs: logs})
			}
			if tcount > 0 {
				mux.Post(core.PendingStateEvent{})
			}
		}(cpy, env.tcount)
	}
}

func (env *Work) commitTransaction(tx *types.Transaction, bc *core.BlockChain, coinbase common.Address, gp *core.GasPool) (error, []*types.Log) {
	snap := env.pubState.Snapshot()
	snapPriv := env.privState.Snapshot()

	pubReceipt, privReceipt, _, err := core.ApplyTransaction(env.config, bc, &coinbase, gp, env.pubState, env.privState, env.remoteDB,
		env.header, tx, &env.header.GasUsed, vm.Config{}, env.accm)
	if err != nil {
		env.pubState.RevertToSnapshot(snap)
		env.privState.RevertToSnapshot(snapPriv)
		return err, nil
	}
	env.txs = append(env.txs, tx)
	env.pubReceipts = append(env.pubReceipts, pubReceipt)
	if privReceipt != nil {
		env.privReceipts = append(env.privReceipts, privReceipt)
	}

	// TODO: consider whether append private logs to returned logs together.
	return nil, pubReceipt.Logs
}
