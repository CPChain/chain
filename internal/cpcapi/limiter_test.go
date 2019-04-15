package core

import (
	"fmt"
	"sync"
	"testing"
	"time"
)

func TestTokenBucket(t *testing.T) {

	var wg sync.WaitGroup
	var lr TokenBucket
	lr.Set(5, 6)

	time.Sleep(time.Second)
	for i := 0; i < 10; i++ {
		wg.Add(1)

		fmt.Println("Create req", i, time.Now())
		go func(i int) {
			if lr.Allow() {
				fmt.Println("--rspn req", i, time.Now())
			}
			wg.Done()
		}(i)

		time.Sleep(100 * time.Millisecond)
	}
	wg.Wait()
}
