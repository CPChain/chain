package syncer

import (
	"sync"
	"testing"
)

func TestQueuePutAndGet(t *testing.T) {
	q := newQueue(2)

	wg := sync.WaitGroup{}
	defer wg.Wait()

	wg.Add(1)

	q.put(resultTask{"test"})
	q.put(resultTask{"test1"})
	q.put(resultTask{"test2"})

	go func() {
		defer wg.Done()
		for !q.empty() {
			task, _ := q.get()
			t.Log(task.data.(string))
		}
	}()
}

func TestClearQueue(t *testing.T) {
	q := newQueue(100)
	q.put(resultTask{"test"})
	q.put(resultTask{"test1"})
	q.put(resultTask{"test2"})

	if q.size != 3 {
		t.Error("queue size is error")
	}

	q.clear()

	if !q.empty() {
		t.Error("queue must be empty")
	}
}

func TestQueueGetTimeout(t *testing.T) {
	q := newQueue(100)
	_, err := q.get()
	if err != ErrTimeout {
		t.Error("err must be ErrTimeout")
	}
}
