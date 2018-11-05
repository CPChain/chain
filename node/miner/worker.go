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

	workCh        chan *Work
	stop          chan struct{}
	quitCurrentOp chan struct{}
	returnCh      chan<- *Result

	chain consensus.ChainReader
	cons  consensus.Engine

	isMining int32 // isMining indicates whether the agent is currently mining
}

func NewNativeWorker(chain consensus.ChainReader, cons consensus.Engine) *NativeWorker {
	miner := &NativeWorker{
		chain:  chain,
		cons:   cons,
		stop:   make(chan struct{}, 1),
		workCh: make(chan *Work, 1),
	}
	return miner
}

func (self *NativeWorker) Work() chan<- *Work            { return self.workCh }
func (self *NativeWorker) SetReturnCh(ch chan<- *Result) { self.returnCh = ch }

func (self *NativeWorker) Stop() {
	if !atomic.CompareAndSwapInt32(&self.isMining, 1, 0) {
		return // agent already stopped
	}
	self.stop <- struct{}{}
done:
	// Empty work channel
	for {
		select {
		case <-self.workCh:
		default:
			break done
		}
	}
}

func (self *NativeWorker) Start() {
	if !atomic.CompareAndSwapInt32(&self.isMining, 0, 1) {
		return // agent already started
	}
	go self.update()
}

func (self *NativeWorker) update() {
out:
	for {
		select {
		case work := <-self.workCh:
			self.mu.Lock()
			if self.quitCurrentOp != nil {
				close(self.quitCurrentOp)
			}
			self.quitCurrentOp = make(chan struct{})
			go self.mine(work, self.quitCurrentOp)
			self.mu.Unlock()
		case <-self.stop:
			self.mu.Lock()
			if self.quitCurrentOp != nil {
				close(self.quitCurrentOp)
				self.quitCurrentOp = nil
			}
			self.mu.Unlock()
			break out
		}
	}
}

func (self *NativeWorker) mine(work *Work, stop <-chan struct{}) {
	if result, err := self.cons.Seal(self.chain, work.Block, stop); result != nil {
		log.Info("Successfully sealed new block", "number", result.Number(), "hash", result.Hash().Hex())
		self.returnCh <- &Result{work, result}
	} else {
		if err != nil {
			if err == consensus.ErrUnauthorized {
				log.Debug("Not your turn", "err", err)
			} else {
				log.Warn("Block sealing failed", "err", err)
			}
		}
		self.returnCh <- nil
	}
}
