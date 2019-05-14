// Copyright 2018 The cpchain authors

package primitives_test

import (
	"crypto/ecdsa"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/primitives"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

const (
	expectedRankResult  = 11
	expectedVolume      = 22
	expectedMaintenance = 33
	expectedUploadCount = 44
	expectedProxyCount  = 55
	expectedIsProxy     = 1
)

var (
	key, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	addr   = crypto.PubkeyToAddress(key.PublicKey)
)

func deployPrimitiveSample(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	deployTransactor.Value = amount
	addr, _, _, err := DeployPrimitiveContractsTest(deployTransactor, backend)
	if err != nil {
		return common.Address{}, err
	}
	backend.Commit()
	return addr, nil
}

type fakePrimitiveBackend struct {
	rank        int64
	txVolume    int64
	maintenance int64
	uploadCount int64
	proxyCount  int64
	isProxy     int64

	lastParameter struct {
		address common.Address
		number  uint64
	}
}

func (b *fakePrimitiveBackend) Rank(address common.Address, number uint64) (int64, error) {
	b.recordParameters(address, number)
	return b.rank, nil
}

func (b *fakePrimitiveBackend) TxVolume(address common.Address, number uint64) (int64, error) {
	b.recordParameters(address, number)
	return b.txVolume, nil
}

func (b *fakePrimitiveBackend) Maintenance(address common.Address, number uint64) (int64, error) {
	b.recordParameters(address, number)
	return b.maintenance, nil
}

func (b *fakePrimitiveBackend) UploadCount(address common.Address, number uint64) (int64, error) {
	b.recordParameters(address, number)
	return b.uploadCount, nil
}

func (b *fakePrimitiveBackend) ProxyInfo(address common.Address, number uint64) (int64, int64, error) {
	b.recordParameters(address, number)
	return b.isProxy, b.proxyCount, nil
}

func (b *fakePrimitiveBackend) recordParameters(address common.Address, number uint64) {
	b.lastParameter.address = address
	b.lastParameter.number = number
}

var mockBackend *fakePrimitiveBackend

func registerPrimitiveContracts() {
	mockBackend = &fakePrimitiveBackend{
		rank:        expectedRankResult,
		txVolume:    expectedVolume,
		maintenance: expectedMaintenance,
		uploadCount: expectedUploadCount,
		proxyCount:  expectedProxyCount,
		isProxy:     expectedIsProxy,
	}
	vm.RegisterPrimitiveContract(common.BytesToAddress([]byte{100}), &primitives.GetRank{Backend: mockBackend})
	vm.RegisterPrimitiveContract(common.BytesToAddress([]byte{101}), &primitives.GetMaintenance{Backend: mockBackend})
	vm.RegisterPrimitiveContract(common.BytesToAddress([]byte{102}), &primitives.GetProxyCount{Backend: mockBackend})
	vm.RegisterPrimitiveContract(common.BytesToAddress([]byte{103}), &primitives.GetUploadReward{Backend: mockBackend})
	vm.RegisterPrimitiveContract(common.BytesToAddress([]byte{104}), &primitives.GetTxVolume{Backend: mockBackend})
	vm.RegisterPrimitiveContract(common.BytesToAddress([]byte{105}), &primitives.IsProxy{Backend: mockBackend})
}

func TestDeployPrimitiveContracts(t *testing.T) {
	registerPrimitiveContracts()

	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	primitiveAddr, err := deployPrimitiveSample(key, big.NewInt(0), contractBackend)
	checkError(t, "deploy contract: expected no error, got %v", err)

	primitiveContracts, err := NewPrimitiveContractsTest(primitiveAddr, contractBackend)
	checkError(t, "can't deploy root registry: %v", err)
	//	_ = contractAddr
	contractBackend.Commit()

	//	contractBackend.SendTransaction(contractBackend)
	//TODO:need add more test  @HMW
	//maximumNoc
	rank, err := primitiveContracts.GetRank(nil, addr, new(big.Int).SetUint64(2))
	log.Debugf("GetRank: %v", rank)
	checkError(t, "GetRank error: %v", err)
	if rank.Uint64() != expectedRankResult {
		t.Error("Expected", expectedRankResult, ", but got", rank)
	}
	checkPassedParams(t, addr, 2)

	tx, err := primitiveContracts.GetTxVolume(nil, addr, new(big.Int).SetUint64(1))
	log.Debugf("GetTxVolume: %v", tx)
	checkError(t, "GetTxVolume error: %v", err)
	if tx.Uint64() != expectedVolume {
		t.Error("Expected", expectedVolume, ", but got", tx)
	}
	checkPassedParams(t, addr, 1)

	pr, err := primitiveContracts.GetProxyCount(nil, addr, new(big.Int).SetUint64(3))
	log.Debugf("GetProxyInfo: %v", pr)
	checkError(t, "GetProxyInfo error: %v", err)
	if pr.Uint64() != expectedProxyCount {
		t.Error("Expected", expectedProxyCount, ", but got", pr)
	}
	checkPassedParams(t, addr, 3)

	ip, err := primitiveContracts.IsProxy(nil, addr, new(big.Int).SetUint64(2))
	log.Debugf("GetIsProxyInfo: %v", ip)
	checkError(t, "GetISProxyInfo error: %v", err)
	if ip.Uint64() != expectedIsProxy {
		t.Error("Expected", expectedIsProxy, ", but got", ip)
	}
	checkPassedParams(t, addr, 2)

	ur, err := primitiveContracts.GetUploadInfo(nil, addr, new(big.Int).SetUint64(4))
	log.Debugf("GetUploadInfo: %v", ur)
	checkError(t, "GetUploadInfo error: %v", err)
	if ur.Uint64() != expectedUploadCount {
		t.Error("Expected", expectedUploadCount, ", but got", ur)
	}
	checkPassedParams(t, addr, 4)

	addr2 := common.BytesToAddress([]byte{10, 10, 20, 20})
	mt, err := primitiveContracts.GetMaintenance(nil, addr2, new(big.Int).SetUint64(2))
	log.Debugf("GetMaintenance: %v", mt)
	checkError(t, "GetMaintenance error: %v", err)
	if mt.Uint64() != expectedMaintenance {
		t.Error("Expected", expectedMaintenance, ", but got", mt)
	}
	checkPassedParams(t, addr2, 2)
}

func checkError(t *testing.T, msg string, err error) {
	if err != nil {
		t.Fatalf(msg, err)
	}
}

func checkPassedParams(t *testing.T, addr common.Address, number uint64) {
	if mockBackend.lastParameter.address != addr {
		t.Errorf("Want address %s, but got %s", addr.Hex(), mockBackend.lastParameter.address.Hex())
	}
	if mockBackend.lastParameter.number != number {
		t.Errorf("Want block number %d, but got %d", number, mockBackend.lastParameter.number)
	}
}
