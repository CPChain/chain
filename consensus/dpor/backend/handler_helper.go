package backend

import (
	"errors"

	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	lru "github.com/hashicorp/golang-lru"
)

const (
	maxKnownBlocks = 256
)

var (
	errNilBlock = errors.New("nil block")
)

type blockIdentifier struct {
	number uint64
	hash   common.Hash
}

// RecentBlocks caches recent received blocks
type RecentBlocks struct {
	blocks           *lru.ARCCache
	futureBlocks     *lru.ARCCache // futureBlocks will only be called by single goroutine
	unknownAncestors *lru.ARCCache // unknownAncestors is the same as futureBlocks
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

	if block == nil {
		return errNilBlock
	}

	bi := blockIdentifier{
		hash:   block.Hash(),
		number: block.NumberU64(),
	}

	rb.blocks.Add(bi, block)

	return nil
}

// AddFutureBlock adds a block to caches
func (rb *RecentBlocks) AddFutureBlock(block *types.Block) error {

	if block == nil {
		return errNilBlock
	}

	bi := blockIdentifier{
		hash:   block.Hash(),
		number: block.NumberU64(),
	}

	rb.futureBlocks.Add(bi, block)

	return nil
}

// AddUnknownAncestor adds a block to caches
func (rb *RecentBlocks) AddUnknownAncestor(block *types.Block) error {

	if block == nil {
		return errNilBlock
	}
	bi := blockIdentifier{
		hash:   block.Hash(),
		number: block.NumberU64(),
	}

	rb.unknownAncestors.Add(bi, block)

	return nil
}

// GetBlock returns a block
func (rb *RecentBlocks) GetBlock(bi blockIdentifier) (*types.Block, error) {

	if blk, ok := rb.blocks.Get(bi); ok {
		return blk.(*types.Block), nil
	}

	return nil, errNilBlock
}

// GetFutureBlock returns a future block
func (rb *RecentBlocks) GetFutureBlock(bi blockIdentifier) (*types.Block, error) {

	if blk, ok := rb.futureBlocks.Get(bi); ok {
		return blk.(*types.Block), nil
	}

	return nil, errNilBlock

}

// GetUnknownAncestor returns an unknown ancestor block
func (rb *RecentBlocks) GetUnknownAncestor(bi blockIdentifier) (*types.Block, error) {

	if blk, ok := rb.unknownAncestors.Get(bi); ok {
		return blk.(*types.Block), nil
	}

	return nil, errNilBlock
}

// GetFutureBlockNumbers adds a block to caches
func (rb *RecentBlocks) GetFutureBlockIdentifiers() []interface{} {
	return rb.futureBlocks.Keys()
}

// GetUnknownAncestorBlockNumbers returns future block numbers
func (rb *RecentBlocks) GetUnknownAncestorBlockIdentifiers() []interface{} {
	return rb.unknownAncestors.Keys()
}
