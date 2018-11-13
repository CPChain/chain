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
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"math/big"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// cpuWork cpu proof work
type cpuWork struct {
	*pow
}

// newCPUWork returns a new instance of cpuWork
func newCPUWork(config CPUConfig, address common.Address, header *types.Header) *cpuWork {
	return &cpuWork{
		pow: newPow(config.Difficulty, config.LifeTime, address, header),
	}
}

// tryOnce tries the nonce.
func (cpu *cpuWork) tryOnce() bool {
	target := big.NewInt(1)
	target.Lsh(target, 256-uint(cpu.difficulty))

	var hash [32]byte
	data := cpu.makeData()

	hash = sha256.Sum256(data)

	return new(big.Int).SetBytes(hash[:]).Cmp(target) <= 0
}

// makeData wrappers the nonce.
func (cpu *cpuWork) makeData() []byte {
	nonceBytes := make([]byte, 8)
	binary.LittleEndian.PutUint64(nonceBytes, cpu.nonce)

	return bytes.Join(
		[][]byte{
			cpu.address.Bytes(),
			cpu.header.HashNoNonce().Bytes(),
			nonceBytes,
		},
		nil,
	)
}

// prove implements ProveBackend, generate the campaign information.
// starts cpu pow work.
func (cpu *cpuWork) prove(abort chan struct{}, wg *sync.WaitGroup) {
	defer wg.Done()
	ticker := time.NewTicker(cpu.lifeTime)
	defer ticker.Stop()

search:
	for {
		select {
		case <-abort:
			cpu.err = errors.New("proof work aborts")
			break search
		case <-ticker.C:
			close(abort)
			cpu.err = errors.New("proof work timeout")
			break search
		default:
			if cpu.nonce < maxNonce && cpu.tryOnce() {
				break search
			}
			cpu.nonce++
		}
	}
}

// getProofInfo return the cpu pow result
func (cpu *cpuWork) getProofInfo() uint64 {
	return cpu.nonce
}
