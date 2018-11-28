package backend

import (
	"errors"
	"sync"

	"bitbucket.org/cpchain/chain/types"
)

const (
	maxKnownBlocks = 3
)

var (
	errNilBlock = errors.New("nil block")
)

type BlockStatus uint8

const (
	Pending BlockStatus = iota
	Inserted
	Wrong
)

type KnownBlock struct {
	*types.Block
	Status BlockStatus
}

type RecentBlocks struct {
	blocks map[uint64]*KnownBlock
	latest uint64
	first  uint64
	lock   sync.RWMutex
}

func newKnownBlocks() *RecentBlocks {
	return &RecentBlocks{
		blocks: make(map[uint64]*KnownBlock),
		latest: 0,
		first:  0,
	}
}

func (rb *RecentBlocks) AddBlock(block *types.Block) error {
	rb.lock.Lock()
	defer rb.lock.Unlock()

	if block == nil {
		return errNilBlock
	}

	number := block.NumberU64()

	kb := &KnownBlock{
		Block:  block,
		Status: Pending,
	}

	rb.blocks[number] = kb

	if number == rb.first+maxKnownBlocks && rb.blocks[rb.first] != nil {
		delete(rb.blocks, rb.first)
		rb.first++
	}

	return nil
}

func (rb *RecentBlocks) UpdateStatus(number uint64, status BlockStatus) error {
	rb.lock.Lock()
	defer rb.lock.Unlock()

	if rb.blocks[number] == nil {
		return errNilBlock
	}

	rb.blocks[number].Status = status

	if status == Inserted && number > rb.latest {
		rb.latest = number
	}

	return nil
}

func (rb *RecentBlocks) GetKnownBlock(number uint64) (*KnownBlock, error) {
	rb.lock.Lock()
	defer rb.lock.Unlock()

	if rb.blocks[number] == nil || rb.blocks[number].Block == nil {
		return nil, errNilBlock
	}

	return rb.blocks[number], nil
}
