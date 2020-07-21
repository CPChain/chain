package syncer

import (
	"sync"
	"testing"
	"time"
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

func TestQueueMultiPut(t *testing.T) {
	var (
		routineCnt = 10
		dataCnt    = 5
	)
	q := newQueue(1000)

	wg := sync.WaitGroup{}
	defer wg.Wait()
	wg.Add(1)

	for i := 0; i < routineCnt; i++ {
		wg.Add(1)
		go func(base int) {
			defer wg.Done()
			for i := 0; i < dataCnt; i++ {
				value := base*dataCnt + i
				q.put(resultTask{value})
			}
		}(i)
	}
	<-time.After(time.Second)
	go func() {
		defer wg.Done()
		var array []int
		for !q.empty() {
			task, _ := q.get()
			t.Log(task.data.(int))
			array = append(array, task.data.(int))
		}
		if len(array) != dataCnt*routineCnt {
			t.Errorf("array's length should be %v, but got %v", dataCnt*routineCnt, len(array))
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
