package admission

import (
	"sync"

	"bitbucket.org/cpchain/chain/admission/ethash"
	"bitbucket.org/cpchain/chain/core/types"
	"github.com/ethereum/go-ethereum/common"
)

// memoryWork memory proof work
type memoryWork struct {
	*pow
	ethash *ethash.Ethash
}

// newMemoryWork returns a new memoryWork instance
func newMemoryWork(config ethash.Config, address common.Address, header *types.Header, ethashClient *ethash.Ethash) *memoryWork {
	pow := newPow(config.Difficulty, config.LifeTime, address, header)
	return &memoryWork{
		pow:    pow,
		ethash: ethashClient,
	}
}

// prove implements ProveBackend, generate the campaign information.
// starts memory pow work.
func (memory *memoryWork) prove(abort chan struct{}, wg *sync.WaitGroup) {
	memory.nonce, memory.err = memory.ethash.Seal(memory.header, abort, memory.lifeTime)
}

// getProofInfo return the cpu pow result
func (memory *memoryWork) getProofInfo() uint64 {
	return memory.nonce
}
