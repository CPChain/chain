package backend

import (
	"errors"
	"sync"

	"bitbucket.org/cpchain/chain/types"
	"github.com/hashicorp/golang-lru"
)

const (
	maxKnownBlocks = 256
)

var (
	errNilBlock = errors.New("nil block")
)

// RecentBlocks caches recent received blocks
type RecentBlocks struct {
	blocks    *lru.ARCCache
	blockLock sync.RWMutex

	futureBlocks     *lru.ARCCache // futureBlocks will only be called by single goroutine
	futureBlocksLock sync.RWMutex

	unknownAncestors     *lru.ARCCache // unknownAncestors is the same as futureBlocks
	unknownAncestorsLock sync.RWMutex
}

func newKnownBlocks() *RecentBlocks {
	blocks, _ := lru.NewARC(maxKnownBlocks)
	futureBlocks, _ := lru.NewARC(maxKnownBlocks)
	unknownAncestors, _ := lru.NewARC(maxKnownBlocks)

	return &RecentBlocks{
		blocks:           blocks,
		futureBlocks:     futureBlocks,
		unknownAncestors: unknownAncestors,
	}
}

// AddBlock adds a block to caches
func (rb *RecentBlocks) AddBlock(block *types.Block) error {
	rb.blockLock.Lock()
	defer rb.blockLock.Unlock()

	if block == nil {
		return errNilBlock
	}

	number := block.NumberU64()
	rb.blocks.Add(number, block)

	return nil
}

// AddFutureBlock adds a block to caches
func (rb *RecentBlocks) AddFutureBlock(block *types.Block) error {
	rb.futureBlocksLock.Lock()
	defer rb.futureBlocksLock.Unlock()

	if block == nil {
		return errNilBlock
	}

	number := block.NumberU64()
	rb.futureBlocks.Add(number, block)

	return nil
}

// AddUnknownAncestor adds a block to caches
func (rb *RecentBlocks) AddUnknownAncestor(block *types.Block) error {
	rb.unknownAncestorsLock.Lock()
	defer rb.unknownAncestorsLock.Unlock()

	if block == nil {
		return errNilBlock
	}

	number := block.NumberU64()
	rb.unknownAncestors.Add(number, block)

	return nil
}

// GetBlock returns a block
func (rb *RecentBlocks) GetBlock(number uint64) (*types.Block, error) {
	rb.blockLock.RLock()
	defer rb.blockLock.RUnlock()

	if blk, ok := rb.blocks.Get(number); ok {
		return blk.(*types.Block), nil
	}

	return nil, errNilBlock
}

// GetFutureBlock returns a future block
func (rb *RecentBlocks) GetFutureBlock(number uint64) (*types.Block, error) {
	rb.futureBlocksLock.RLock()
	defer rb.futureBlocksLock.RUnlock()

	if blk, ok := rb.futureBlocks.Get(number); ok {
		return blk.(*types.Block), nil
	}

	return nil, errNilBlock

}

// GetUnknownAncestor returns an unknown ancestor block
func (rb *RecentBlocks) GetUnknownAncestor(number uint64) (*types.Block, error) {
	rb.unknownAncestorsLock.RLock()
	defer rb.unknownAncestorsLock.RUnlock()

	if blk, ok := rb.unknownAncestors.Get(number); ok {
		return blk.(*types.Block), nil
	}

	return nil, errNilBlock
}

// GetFutureBlockNumbers adds a block to caches
func (rb *RecentBlocks) GetFutureBlockNumbers() []interface{} {
	rb.futureBlocksLock.RLock()
	defer rb.futureBlocksLock.RUnlock()

	return rb.futureBlocks.Keys()

}

// GetUnknownAncestorBlockNumbers returns future block numbers
func (rb *RecentBlocks) GetUnknownAncestorBlockNumbers() []interface{} {
	rb.unknownAncestorsLock.RLock()
	defer rb.unknownAncestorsLock.RUnlock()

	return rb.unknownAncestors.Keys()
}
