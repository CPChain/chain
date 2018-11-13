// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package admission

import (
	"sync"

	"bitbucket.org/cpchain/chain/admission/ethash"
	"bitbucket.org/cpchain/chain/types"
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
