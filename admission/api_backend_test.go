package admission_test

import (
	"crypto/ecdsa"
	"math/big"
	"reflect"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/admission"
	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	key      *ecdsa.PrivateKey
	addr     common.Address
	key1, _  = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	addr1    = crypto.PubkeyToAddress(key1.PublicKey)
	keyPath  = "../examples/cpchain/conf/keys"
	password = "password"
	ks       *keystore.KeyStore

	alloc = core.GenesisAlloc{
		addr:  {Balance: big.NewInt(1000000000)},
		addr1: {Balance: big.NewInt(1000000000)},
	}
	// gspec = core.Genesis{Config: params.TestChainConfig, Alloc: alloc}
	gspec   = core.Genesis{Config: configs.ChainConfigInfo(), Alloc: alloc}
	testdb  = database.NewMemDatabase()
	genesis = gspec.MustCommit(testdb)
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

func newChainReader(alloc core.GenesisAlloc) consensus.ChainReader {
	_, _ = core.GenerateChain(configs.TestChainConfig, genesis, dpor.New(&configs.DporConfig{}, testdb), testdb, nil, 8, nil)
	chain, _ := core.NewBlockChain(testdb, nil, configs.TestChainConfig, dpor.New(&configs.DporConfig{}, testdb), vm.Config{}, nil, nil)

	return chain
}

func getStatus(ac *admission.AdmissionControl) (admission.WorkStatus, error) {
	time.Sleep(50 * time.Millisecond)
	status, err := ac.GetStatus()
	return status, err
}

func newTestBackend() *backends.SimulatedBackend {
	return backends.NewDporSimulatedBackend(core.GenesisAlloc{
		addr:  {Balance: big.NewInt(1000000000)},
		addr1: {Balance: big.NewInt(1000000000)},
	})
}

// newAC return a new AdmissionControl instance
func newAcApiBackend(cpuDifficulty uint64, cpuLifeTime int64, memoryDifficulty uint64, memoryLifeTime int64) admission.ApiBackend {
	config := admission.DefaultConfig
	if cpuDifficulty != 0 {
		config.CpuDifficulty = cpuDifficulty
	}

	if cpuLifeTime != 0 {
		config.CpuLifeTime = time.Duration(cpuLifeTime) * time.Second
	}

	if memoryDifficulty != 0 {
		config.MemoryDifficulty = memoryDifficulty
	}

	if memoryLifeTime != 0 {
		config.MemoryCpuLifeTime = time.Duration(memoryLifeTime) * time.Second
	}

	return admission.NewAdmissionApiBackend(newChainReader(alloc), addr, config)
}

// TestAPIs test apis
func TestApis(t *testing.T) {
	ac := newAcApiBackend(0, 0, 0, 0)
	apis := ac.Apis()

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
	ac := newAcApiBackend(0, 0, 0, 0)
	status, err := ac.GetStatus()
	var wantErr error
	if status != admission.AcIdle || !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("Before starting campaign: GetStatus, want(status:%d, err:%v), but(status:%d, err:%v)\n", admission.AcIdle, wantErr, status, err)
	}

	ac.Campaign()
	status, err = ac.GetStatus()
	if status != admission.AcRunning || !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("Started compaign: GetStatus, want(status:%d, err:%v), but(status:%d, err:%v)\n", admission.AcRunning, wantErr, status, err)
	}

	ac.Abort()
	status, err = ac.GetStatus()
	if status != admission.AcIdle || !reflect.DeepEqual(err, wantErr) {
		t.Fatalf("Aborted campaign: GetStatus, want(status:%d, err:%v), but(status:%d, err:%v)\n", admission.AcIdle, wantErr, status, err)
	}
}
