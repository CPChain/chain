// Copyright 2018 The cpchain authors
// Copyright 2015 The go-ethereum Authors

package miner

import (
	"sync"
	"sync/atomic"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
)

type NativeWorker struct {
	mu sync.Mutex

	workCh          chan *Work // miner.engine must call this to send in work
	quitCh          chan struct{}
	quitCurrentOpCh chan struct{}
	returnCh        chan<- *Result // miner.engine must set this to retrieve the mined block

	chain consensus.ChainReader // need to access blocks
	cons  consensus.Engine      // need to seal methods

	isMining int32 // isMining indicates whether the agent is currently mining
}

func NewNativeWorker(chain consensus.ChainReader, cons consensus.Engine) *NativeWorker {
	worker := &NativeWorker{
		chain:  chain,
		cons:   cons,
		workCh: make(chan *Work, 1),
		quitCh: make(chan struct{}, 1),
	}
	return worker
}

func (nw *NativeWorker) Work() chan<- *Work            { return nw.workCh }
func (nw *NativeWorker) SetReturnCh(ch chan<- *Result) { nw.returnCh = ch }

func (nw *NativeWorker) Stop() {
	if !atomic.CompareAndSwapInt32(&nw.isMining, 1, 0) {
		return // worker already stopped
	}
	nw.quitCh <- struct{}{}
done:
	// empty work channel
	for {
		select {
		case <-nw.workCh:
		default:
			break done
		}
	}
}

func (nw *NativeWorker) Start() {
	// ensure no start twice
	if !atomic.CompareAndSwapInt32(&nw.isMining, 0, 1) {
		return
	}
	go nw.update()
}

// update spawns a new goroutine to mine blocks and abort the previous mining goroutines.
func (nw *NativeWorker) update() {
out:
	for {
		select {
		case work := <-nw.workCh:
			nw.mu.Lock()

			if nw.quitCurrentOpCh != nil {
				// abort the current mining operations
				close(nw.quitCurrentOpCh)
			}
			nw.quitCurrentOpCh = make(chan struct{})
			// spawn a new go routine to mine the blocks
			nw.mine(work, nw.quitCurrentOpCh)

			nw.mu.Unlock()

		case <-nw.quitCh:
			nw.mu.Lock()
			// signal the mining goroutines to quit
			if nw.quitCurrentOpCh != nil {
				close(nw.quitCurrentOpCh)
				nw.quitCurrentOpCh = nil
			}
			nw.mu.Unlock()
			break out
		}
	}
}

// mine invokes the consensus engine to seal a block.
// note, finalize is called in miner's engine, not here.
func (nw *NativeWorker) mine(work *Work, quitCh <-chan struct{}) {
	if result, err := nw.cons.Seal(nw.chain, work.Block, quitCh); result != nil {
		log.Info("Successfully sealed new block", "number", result.Number(), "hash", result.Hash().Hex())
		nw.returnCh <- &Result{work, result}
	} else {
		if err != nil {
			if err == consensus.ErrUnauthorized {
				log.Info("Not your turn", "err", err, "number", work.Block.Number())
			} else if err == consensus.ErrNotInProposerCommittee {
				log.Info("Not in proposer committee", "err", err, "number", work.Block.Number())
			} else {
				log.Warn("Block sealing failed", "err", err)
			}
		}
		// ok. failed to seal.
		nw.returnCh <- nil
	}
}
