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
	"errors"
	"fmt"
	"math/big"
	"reflect"
	"sync"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/admission/ethash"
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/core"
)

func newMemory(config ethash.Config) *memoryWork {
	alloc := core.GenesisAlloc{
		addr: {Balance: big.NewInt(1000000000)},
	}
	chain := newChainReader(alloc)
	return newMemoryWork(config, common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"), chain.CurrentHeader(), ethash.New(DefaultEthashConfig, chain))
}

// TestMemoryProve tests memory sub work prove
func TestMemoryProve(t *testing.T) {
	memory := newMemory(DefaultEthashConfig)
	abort := make(chan struct{})
	wg := new(sync.WaitGroup)

	wg.Add(1)
	memory.prove(abort, wg)
	wg.Wait()

	if memory.nonce != 17 {
		t.Fatalf("want 17, but %d", memory.nonce)
	}
}

// TestMemoryProveAbort tests memory sub work when sends abort signal
func TestMemoryProveAbort(t *testing.T) {
	memory := newMemory(DefaultEthashConfig)

	abort := make(chan struct{})
	wg := new(sync.WaitGroup)
	wg.Add(1)
	go memory.prove(abort, wg)
	close(abort)
	wg.Wait()
	wantErr := errors.New("proof work aborts")
	err := memory.getError()
	if !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("memory.Prove want(%v), but(%v)", wantErr, err)
	}
}

// TestMemoryProveTimeOut tests prove when timeout
func TestMemoryProveTimeout(t *testing.T) {
	DefaultEthashConfig.LifeTime = 4 * time.Second
	memory := newMemory(DefaultEthashConfig)
	abort := make(chan struct{})
	wg := new(sync.WaitGroup)
	wg.Add(1)

	ticker := time.NewTicker(1 * time.Second)
	go func() {
		for t := range ticker.C {
			fmt.Println("tick at", t)
		}
	}()

	memory.prove(abort, wg)
	if memory.getError() != nil {
		t.Fatal("want err, but nil")
	}
}
