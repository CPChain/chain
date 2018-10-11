package admission

import (
	"errors"
	"math/big"
	"reflect"
	"sync"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/core"
	"github.com/ethereum/go-ethereum/common"
)

func newCPU() *cpuWork {
	alloc := core.GenesisAlloc{
		addr: {Balance: big.NewInt(1000000000)},
	}
	chain := newChainReader(alloc)
	config := CPUConfig{
		Difficulty: 5,
		LifeTime:   1 * 60 * time.Second,
	}
	return newCPUWork(config, common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"), chain.CurrentHeader())
}

// TestCPUProve tests cpu sub work prove
func TestCPUProve(t *testing.T) {
	cpu := newCPU()
	abort := make(chan struct{})
	wg := new(sync.WaitGroup)

	wg.Add(1)
	cpu.prove(abort, wg)
	wg.Wait()

	if cpu.nonce != 1 {
		t.Fatalf("want 1, but %d", cpu.nonce)
	}
}

// TestCPUProveAbort tests cpu sub work when sends abort signal
func TestCPUProveAbort(t *testing.T) {
	cpu := newCPU()

	abort := make(chan struct{})
	wg := new(sync.WaitGroup)
	wg.Add(1)
	go cpu.prove(abort, wg)
	close(abort)
	wg.Wait()
	wantErr := errors.New("proof work aborts")
	err := cpu.getError()
	if !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("cpu.Prove want(%v), but(%v)", wantErr, err)
	}
}

// TestCPUProveTimeOut tests prove when timeout
func TestCPUProveTimeout(t *testing.T) {
	cpu := newCPU()
	abort := make(chan struct{})
	wg := new(sync.WaitGroup)
	wg.Add(1)
	cpu.prove(abort, wg)
	if cpu.getError() != nil {
		t.Fatal("want err, but nil")
	}
}
