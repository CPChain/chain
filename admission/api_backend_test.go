package admission

import (
	"errors"
	"math/big"
	"reflect"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/consensus/ethash"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/types"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/ethdb"
	"bitbucket.org/cpchain/chain/params"
	"bitbucket.org/cpchain/chain/rpc"
)

const testAddress = "0x9f5c1040c24a8f3333dac03077d3c5e755b32571"

type MockBackend struct {
	blockChain *core.BlockChain
}

func newMockBackend() *MockBackend {
	var (
		pow           = ethash.NewFaker()
		db            = ethdb.NewMemDatabase()
		config        = &params.ChainConfig{DAOForkBlock: big.NewInt(1), DAOForkSupport: false}
		gspec         = &core.Genesis{Config: config}
		genesis       = gspec.MustCommit(db)
		blockChain, _ = core.NewBlockChain(db, nil, config, pow, vm.Config{})
	)

	core.GenerateChain(&params.ChainConfig{}, genesis, pow, db, 1, nil)
	return &MockBackend{
		blockChain: blockChain,
	}
}

func (b *MockBackend) CurrentBlock() *types.Block {
	return b.blockChain.CurrentBlock()
}

func getStatus(ac *AdmissionControl) (workStatus, error) {
	time.Sleep(50 * time.Millisecond)
	status, err := ac.GetStatus()
	return status, err
}

// newAC return a new AdmissionControl instance
func newAC(cpuDifficulty, cpuLifeTime, memoryDifficulty, memoryLifeTime int64) *AdmissionControl {
	config := DefaultConfig
	if cpuDifficulty == 0 {
		cpuDifficulty = 255
	}

	if cpuLifeTime == 0 {
		cpuLifeTime = 255
	}

	if memoryDifficulty == 0 {
		memoryDifficulty = 255
	}

	if memoryLifeTime == 0 {
		memoryLifeTime = 255
	}
	config.CPULifeTime = time.Duration(cpuLifeTime) * time.Millisecond
	config.MemoryDifficulty = memoryDifficulty
	config.CPUDifficulty = cpuDifficulty
	config.MemoryLifeTime = time.Duration(memoryLifeTime) * time.Millisecond
	return NewAdmissionControl(newMockBackend(), common.HexToAddress(testAddress), config)
}

// TestAPIs test apis
func TestAPIs(t *testing.T) {
	ac := newAC(0, 0, 0, 0)
	apis := ac.APIs()

	wantApis := []rpc.API{
		{
			Namespace: "admission",
			Version:   "1.0",
			Service:   ac,
			Public:    false,
		},
	}
	if !reflect.DeepEqual(apis, wantApis) {
		t.Fatalf("ac.APIs want(%+v), but(%+v)", wantApis, apis)
	}
}

// TestCampaign tests campaign, check status, abort and check status
func TestCampaign(t *testing.T) {
	ac := newAC(0, 0, 0, 0)
	ac.Campaign()
	status, err := getStatus(ac)
	var wantErr error
	if status != AcRunning || !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("start Campaign then GetStatus, want(status:%d, err:%v), but(status:%d, err:%v)\n", AcRunning, wantErr, status, err)
	}
}

// TestCampaign_Timeout timeout when campaign
func TestCampaign_Timeout(t *testing.T) {
	ac := newAC(0, 10, 0, 10)
	ac.Campaign()

	status, err := getStatus(ac)
	wantStatus, wantErr := AcIdle, errors.New("proof work timeout")
	if status != wantStatus || !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("start Campaign, want(status:%d,err:%v), but(status:%d, err:%v)", AcIdle, wantErr, status, err)
	}
}

// TestAbort_Twice twice campaign
func TestCampaign_Twice(t *testing.T) {
	ac := newAC(0, 0, 0, 0)
	ac.Campaign()
	status, err := getStatus(ac)
	var wantErr error
	if status != AcRunning || !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("start Campaign then GetStatus, want(status:%d, err:%v), but(status:%d, err:%v)\n", AcRunning, wantErr, status, err)
	}

	ac.Campaign()
	status, err = getStatus(ac)
	if status != AcRunning || !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("start Campaign then GetStatus, want(status:%d, err:%v), but(status:%d, err:%v)\n", AcRunning, wantErr, status, err)
	}
}

// TestAbort_TimeoutAndAbort tests abort when no campaign starts
func TestAbort_NoCampaign(t *testing.T) {
	ac := newAC(0, 0, 0, 0)
	status, err := getStatus(ac)
	var wantErr error
	if status != AcIdle || !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("start Campaign then GetStatus, want(status:%d, err:%v), but(status:%d, err:%v)\n", AcIdle, wantErr, status, err)
	}
}

// TestAbort aborts the task, check status
func TestAbort(t *testing.T) {
	ac := newAC(0, 0, 0, 0)
	ac.Campaign()
	status, err := getStatus(ac)
	var wantErr error
	if status != AcRunning || !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("start Campaign then GetStatus, want(status:%d, err:%v), but(status:%d, err:%v)\n", AcRunning, wantErr, status, err)
	}

	ac.Abort()
	wantErr = errors.New("proof work aborts")
	status, err = getStatus(ac)
	if status != AcIdle || !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("start Campaign then Abort, wait all goroutine done to get status, want(status:%d, err:%v), but(status:%d, err:%v)\n", AcIdle, wantErr, status, err)
	}
}

// TestAbort aborts the task, check status
func TestAbort_Twice(t *testing.T) {
	ac := newAC(0, 0, 0, 0)
	ac.Campaign()
	status, err := getStatus(ac)
	var wantErr error
	if status != AcRunning || !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("start Campaign then GetStatus, want(status:%d, err:%v), but(status:%d, err:%v)\n", AcRunning, wantErr, status, err)
	}

	ac.Abort()
	wantErr = errors.New("proof work aborts")
	status, err = getStatus(ac)
	if status != AcIdle || !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("start Campaign then Abort, wait all goroutine done to get status, want(status:%d, err:%v), but(status:%d, err:%v)\n", AcIdle, wantErr, status, err)
	}

	ac.err = nil
	ac.Abort()
	status, err = getStatus(ac)
	if status != AcIdle || err != nil {
		t.Fatalf("start Campaign then twice abort, want(status:%d, err:%v), but(status:%d, err:%v)\n", AcIdle, nil, status, err)
	}
}

// TestGetProofInfo test get proofinfo
func TestGetProofInfo(t *testing.T) {
	ac := newAC(5, 1000, 5, 1000)
	ac.Campaign()
	info := ac.GetProofInfo()

	wantInfo := ProofInfo{
		CPUProofInfo:    CPUProofInfo{},
		MemoryProofInfo: MemoryProofInfo{},
	}

	if !reflect.DeepEqual(wantInfo, info) {
		t.Fatalf("campaign, want(info: %+v), bug(info: %+v)", wantInfo, info)
	}
}
