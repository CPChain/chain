package admission

import (
	"crypto/ecdsa"
	"errors"
	"math/big"
	"reflect"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/contracts/dpor"
	"bitbucket.org/cpchain/chain/crypto"

	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/consensus/ethash"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/types"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/ethdb"
	"bitbucket.org/cpchain/chain/params"
	"bitbucket.org/cpchain/chain/rpc"
)

var (
	key      *ecdsa.PrivateKey
	addr     common.Address
	key1, _  = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	addr1    = crypto.PubkeyToAddress(key1.PublicKey)
	keyPath  = "../examples/cpchain/keys"
	password = "password"
	ks       *keystore.KeyStore

	alloc = core.GenesisAlloc{
		addr:  {Balance: big.NewInt(1000000000)},
		addr1: {Balance: big.NewInt(1000000000)},
	}
	genesis = core.Genesis{Config: params.AllEthashProtocolChanges, Alloc: alloc}
)

func init() {
	ks = keystore.NewKeyStore(keyPath, 2, 1)
	account := ks.Accounts()[0]
	account, key0, err := ks.GetDecryptedKey(account, password)
	if err != nil {
		new(testing.T).Fatal(err.Error())
	}

	ks.Unlock(account, password)

	key = key0.PrivateKey
	addr = crypto.PubkeyToAddress(key.PublicKey)
}

type MockBackend struct {
	blockChain *core.BlockChain
}

func newMockBackend(alloc core.GenesisAlloc) *MockBackend {
	database := ethdb.NewMemDatabase()
	genesis.MustCommit(database)
	blockchain, _ := core.NewBlockChain(database, nil, genesis.Config, ethash.NewFaker(), vm.Config{}, nil)

	core.GenerateChain(&params.ChainConfig{}, blockchain.CurrentBlock(), ethash.NewFaker(), database, nil, 1, func(int, *core.BlockGen) {})

	return &MockBackend{
		blockChain: blockchain,
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

func newTestBackend() *backends.SimulatedBackend {
	return backends.NewSimulatedBackend(core.GenesisAlloc{
		addr:  {Balance: big.NewInt(1000000000)},
		addr1: {Balance: big.NewInt(1000000000)},
	})
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

	return NewAdmissionControl(newMockBackend(alloc), addr, ks, genesis.Config.ChainID, config)
	// return NewAdmissionControl(newMockBackend(alloc), addr, ks, nil, config)
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

	ac.Abort()
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

	ac.Abort()
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

	ac.Abort()
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

	wantInfo := ProofInfo{}

	if !reflect.DeepEqual(wantInfo, info) {
		t.Fatalf("campaign, want(info: %+v), but(info: %+v)", wantInfo, info)
	}

	ac.Abort()
}

func TestSendCampaignProofInfo_ContractBackendNil(t *testing.T) {
	ac := newAC(5, 0, 5, 0)
	ac.contractBackend = nil

	ac.proofInfo = ProofInfo{BlockNumber: 1, CPUNonce: 15, MemoryNonce: 15}
	ac.sendCampaignProofInfo()

	_, err := ac.GetStatus()
	wantErr := errors.New("contractBackend is nil")
	if !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("expected %v, but %v", wantErr, err)
	}
}

// TestSendCampaignProofInfo_AuthNil test if auth failed
func TestSendCampaignProofInfo_AuthNil(t *testing.T) {
	ac := newAC(5, 0, 5, 0)
	backend := newTestBackend()
	ac.contractBackend = backend

	ac.proofInfo = ProofInfo{BlockNumber: 1, CPUNonce: 15, MemoryNonce: 15}

	password = "123456"
	defer func() {
		password = "password"
	}()
	ac.sendCampaignProofInfo()

	_, err := ac.GetStatus()
	if err == nil {
		t.Fatal("expected err not nil, but gets nil")
	}

}

// TestSendCampaignProofInfo
func TestSendCampaignProofInfo_ContractNil(t *testing.T) {
	ac := newAC(5, 0, 5, 0)
	defaultCampaignContractAddress = "0x0000000000000000000000000000000000000000"
	backend := newTestBackend()
	ac.contractBackend = backend

	ac.proofInfo = ProofInfo{BlockNumber: 1, CPUNonce: 15, MemoryNonce: 15}
	ac.sendCampaignProofInfo()

	_, err := ac.GetStatus()
	if err == nil {
		t.Fatal("exceped error, but nil")
	}

	backend.Commit()
}

func TestSendCampaignProofInfoOk(t *testing.T) {
	ac := newAC(5, 0, 5, 0)

	backend := newTestBackend()
	ac.contractBackend = backend

	transactorOpts := bind.NewKeyedTransactor(key)

	_, _, err := dpor.DeployCampaign(transactorOpts, ac.contractBackend)
	if err != nil {
		t.Fatalf("expect no err, but %v", err.Error())
	}

	backend.Commit()

	ac.proofInfo = ProofInfo{BlockNumber: 1, CPUNonce: 15, MemoryNonce: 15}
	ac.sendCampaignProofInfo()

	backend.Commit()

	_, err = ac.GetStatus()
	if err != nil {
		t.Fatalf("exceped error nil, but %v", err.Error())
	}
}
