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

// BlockIdentifier is the identifier to a block
type BlockIdentifier struct {
	number uint64
	hash   common.Hash
}

// NewBlockIdentifier creates a block identifier with given block number and hash
func NewBlockIdentifier(number uint64, hash common.Hash) BlockIdentifier {
	return BlockIdentifier{
		number: number,
		hash:   hash,
	}
}

// RecentBlocks caches recent received blocks
type RecentBlocks struct {
	blocks *lru.ARCCache
	db     database.Database
}

// NewRecentBlocks creates a new block cache object
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

	bi := BlockIdentifier{
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

// RemoveBlock removes a block from caches
func (rb *RecentBlocks) RemoveBlock(bi BlockIdentifier) error {
	rb.blocks.Remove(bi)
	return rb.db.Delete(bi.hash.Bytes())
}

// GetBlock returns a block with given block identifier
func (rb *RecentBlocks) GetBlock(bi BlockIdentifier) (*types.Block, error) {

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

// GetBlockIdentifiers returns a slice of block identifiers in this cache
func (rb *RecentBlocks) GetBlockIdentifiers() []BlockIdentifier {

	var bis []BlockIdentifier
	for _, bi := range rb.blocks.Keys() {
		bis = append(bis, bi.(BlockIdentifier))
	}

	return bis
}

// BlockOrHeader represents a block or a header
type BlockOrHeader struct {
	block  *types.Block
	header *types.Header
}

// NewBOHFromHeader creates a new BlockOrHeader from a header
func NewBOHFromHeader(header *types.Header) *BlockOrHeader {
	return &BlockOrHeader{
		header: header,
	}
}

// NewBOHFromBlock creates a new BlockOrHeader from a block
func NewBOHFromBlock(block *types.Block) *BlockOrHeader {
	return &BlockOrHeader{
		block: block,
	}
}

// IsBlock checks if the boh is a block
func (bh *BlockOrHeader) IsBlock() bool {
	return bh != nil && bh.block != nil
}

// IsHeader checks if the boh is a header
func (bh *BlockOrHeader) IsHeader() bool {
	return bh != nil && bh.header != nil
}

// Number returns number of the boh
func (bh *BlockOrHeader) Number() uint64 {
	if bh.IsBlock() {
		return bh.block.NumberU64()
	} else if bh.IsHeader() {
		return bh.header.Number.Uint64()
	}
	return uint64(0)
}

// Hash returns hash of the boh
func (bh *BlockOrHeader) Hash() common.Hash {
	if bh.IsBlock() {
		return bh.block.Hash()
	} else if bh.IsHeader() {
		return bh.header.Hash()
	}
	return common.Hash{}
}
