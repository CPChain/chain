package cpcapi

import (
	"sync"
	"time"
)

type TokenBucket struct {
	rate         int64
	capacity     int64
	tokens       int64
	lastTokenSec int64

	lock sync.Mutex
}

func (l *TokenBucket) Allow() bool {
	l.lock.Lock()
	defer l.lock.Unlock()

	now := time.Now().Unix()
	l.tokens = l.tokens + (now-l.lastTokenSec)*l.rate
	if l.tokens > l.capacity {
		l.tokens = l.capacity
	}
	l.lastTokenSec = now
	if l.tokens > 0 {
		l.tokens--
		return true
	} else {
		return false
	}
}

func (l *TokenBucket) Set(r, c int64) {
	l.rate = r
	l.capacity = c
	l.tokens = 0
	l.lastTokenSec = time.Now().Unix()
}
