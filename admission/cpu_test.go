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
	mock := newMockBackend(alloc)
	return newCPUWork(5, common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"), mock.CurrentBlock(), 60*time.Second)
}

// TestProve tests cpu sub work prove
func TestProve(t *testing.T) {
	cpu := newCPU()
	abort := make(chan struct{})
	wg := new(sync.WaitGroup)

	wg.Add(1)
	cpu.prove(abort, wg)
	wg.Wait()

	if cpu.nonce != 17 {
		t.Fatalf("want 17, but %d", cpu.nonce)
	}
}

// TestProveAbort tests cpu sub work when sends abort signal
func TestProveAbort(t *testing.T) {
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

// TestProveTimeOut tests prove when timeout
func TestProveTimeout(t *testing.T) {
	cpu := newCPU()
	abort := make(chan struct{})
	wg := new(sync.WaitGroup)
	wg.Add(1)
	cpu.prove(abort, wg)
	if cpu.getError() != nil {
		t.Fatal("want err, but nil")
	}
}
