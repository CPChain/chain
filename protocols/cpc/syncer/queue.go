package syncer

import (
	"errors"
	"sync/atomic"
	"time"

	"bitbucket.org/cpchain/chain/types"
)

var (
	ErrQueueFull = errors.New("queue is full")
)

type resultTask struct {
	data interface{}
}

type blocksWithReceipts struct {
	headers  []*types.Header
	bodies   [][]*types.Transaction
	receipts []types.Receipts
}

type queue struct {
	queue chan resultTask
	size  int32
	limit int32
}

func newQueue(size int) *queue {
	return &queue{
		queue: make(chan resultTask, size),
		size:  0,
		limit: int32(size),
	}
}

func (q *queue) get() (resultTask, error) {
	timer := time.NewTimer(1 * time.Second)
	select {
	case task := <-q.queue:
		atomic.AddInt32(&q.size, -1)
		return task, nil
	case <-timer.C:
		return resultTask{}, ErrTimeout
	}
}

func (q *queue) put(task resultTask) error {
	if atomic.LoadInt32(&q.size) >= q.limit {
		return ErrQueueFull
	}
	q.queue <- task
	atomic.AddInt32(&q.size, 1)
	return nil
}

func (q *queue) empty() bool {
	return atomic.LoadInt32(&q.size) == 0
}

func (q *queue) clear() {
	for !q.empty() {
		q.get()
	}
}
