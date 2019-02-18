package backend

import (
	"errors"

	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
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

func newBlockIdentifier(number uint64, hash common.Hash) blockIdentifier {
	return blockIdentifier{
		number: number,
		hash:   hash,
	}
}

// RecentBlocks caches recent received blocks
type RecentBlocks struct {
	blocks *lru.ARCCache
	db     database.Database
}

func NewRecentBlocks(db database.Database) *RecentBlocks {
	blocks, _ := lru.NewARC(maxKnownBlocks)

	return &RecentBlocks{
		db:     db,
		blocks: blocks,
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

	bytes, err := rlp.EncodeToBytes(block)
	if err != nil {
		return err
	}

	return rb.db.Put(block.Hash().Bytes(), bytes)
}

// GetBlock returns a block
func (rb *RecentBlocks) GetBlock(bi blockIdentifier) (*types.Block, error) {

	if blk, ok := rb.blocks.Get(bi); ok {
		return blk.(*types.Block), nil
	}

	// retrieve from db
	bytes, err := rb.db.Get(bi.hash.Bytes())
	if err == nil {
		var block *types.Block
		err = rlp.DecodeBytes(bytes, &block)
		return block, err
	}

	return nil, errNilBlock
}
