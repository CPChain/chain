package cache

import (
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
)

func TestNewLRUExpireCache1(t *testing.T) {
	contractLookupCache := NewLRUExpireCache(3)
	forceLiveLookupTTL := 1 * time.Second
	contractLookupCache.Add("key1", true, forceLiveLookupTTL)
	v1, gotIt := contractLookupCache.Get("key1")
	assert.True(t, gotIt)
	assert.NotNil(t, v1)

	time.Sleep(1 * time.Second)
	v1, gotIt = contractLookupCache.Get("key1")
	assert.False(t, gotIt)
	assert.Nil(t, v1)
}

func TestNewLRUExpireCache2(t *testing.T) {
	contractLookupCache := NewLRUExpireCache(3)
	forceLiveLookupTTL := 1 * time.Second
	contractLookupCache.Add("key1", true, forceLiveLookupTTL)
	contractLookupCache.Add("key2", true, forceLiveLookupTTL)
	contractLookupCache.Add("key3", true, forceLiveLookupTTL)
	contractLookupCache.Add("key4", true, forceLiveLookupTTL)
	v1, gotIt := contractLookupCache.Get("key1")
	assert.False(t, gotIt)
	assert.Nil(t, v1)
	assert.Equal(t, 3, len(contractLookupCache.Keys()))
}
