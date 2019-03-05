package cache

import (
	"sync"
	"time"

	"github.com/hashicorp/golang-lru"
)

type Clock interface {
	Now() time.Time
}

type realClock struct{}

func (realClock) Now() time.Time { return time.Now() }

type LRUExpireCache struct {
	clock Clock
	cache *lru.Cache
	lock  sync.Mutex
}

// add new element
func (c *LRUExpireCache) Add(key interface{}, value interface{}, ttl time.Duration) {
	c.lock.Lock()
	defer c.lock.Unlock()
	c.cache.Add(key, &cacheEntry{value, c.clock.Now().Add(ttl)})
}

// get unexpired element from lru cache
func (c *LRUExpireCache) Get(key interface{}) (interface{}, bool) {
	c.lock.Lock()
	defer c.lock.Unlock()
	e, ok := c.cache.Get(key)
	if !ok {
		return nil, false
	}
	if c.clock.Now().After(e.(*cacheEntry).expireTime) {
		c.cache.Remove(key)
		return nil, false
	}
	return e.(*cacheEntry).value, true
}

// remove element
func (c *LRUExpireCache) Remove(key interface{}) {
	c.lock.Lock()
	defer c.lock.Unlock()
	c.cache.Remove(key)
}

// get all keys
func (c *LRUExpireCache) Keys() []interface{} {
	c.lock.Lock()
	defer c.lock.Unlock()
	return c.cache.Keys()
}

type cacheEntry struct {
	value      interface{}
	expireTime time.Time
}

// NewLRUExpireCache return Lru cache
func NewLRUExpireCache(maxSize int) *LRUExpireCache {
	return NewLRUExpireCacheWithClock(maxSize, realClock{})
}

// NewLRUExpireCacheWithClock
func NewLRUExpireCacheWithClock(maxSize int, clock Clock) *LRUExpireCache {
	cache, err := lru.New(maxSize)
	if err != nil {
		panic(err)
	}
	return &LRUExpireCache{clock: clock, cache: cache}
}
