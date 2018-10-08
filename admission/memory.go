package admission

import (
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/core/types"
	"github.com/ethereum/go-ethereum/common"
)

// memoryWork memory proof work
type memoryWork struct {
	*pow
}

// newMemoryWork returns a new memoryWork instance
func newMemoryWork(difficulty int64, address common.Address, block *types.Block, lifeTime time.Duration) *memoryWork {
	return &memoryWork{
		pow: newPow(difficulty, address, block, lifeTime),
	}
}

// prove implements ProveBackend, generate the campaign information.
// starts memory pow work.
func (memory *memoryWork) prove(abort chan struct{}, wg *sync.WaitGroup) {
	defer wg.Done()
}

// getProofInfo return the cpu pow result
func (memory *memoryWork) getProofInfo() uint64 {
	return memory.nonce
}
