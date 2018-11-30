package backend

import (
	"errors"
	"sync"

	"bitbucket.org/cpchain/chain/types"
	lru "github.com/hashicorp/golang-lru"
)

const (
	maxKnownBlocks = 256
)

var (
	errNilBlock = errors.New("nil block")
)

// RecentBlocks caches recent received blocks
type RecentBlocks struct {
	blocks *lru.ARCCache
	latest uint64
	first  uint64
	lock   sync.RWMutex
}

func newKnownBlocks() *RecentBlocks {
	blocks, _ := lru.NewARC(maxKnownBlocks)

	return &RecentBlocks{
		blocks: blocks,
		latest: 0,
		first:  0,
	}
}

// AddBlock adds a block to caches
func (rb *RecentBlocks) AddBlock(block *types.Block) error {
	rb.lock.Lock()
	defer rb.lock.Unlock()

	if block == nil {
		return errNilBlock
	}

	number := block.NumberU64()
	rb.blocks.Add(number, block)

	return nil
}

// GetBlock returns a block
func (rb *RecentBlocks) GetBlock(number uint64) (*types.Block, error) {
	rb.lock.Lock()
	defer rb.lock.Unlock()

	if blk, ok := rb.blocks.Get(number); ok {
		return blk.(*types.Block), nil
	}

	return nil, errNilBlock
}
