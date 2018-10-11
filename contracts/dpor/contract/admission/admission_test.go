package campaignVerify

import (
	"crypto/ecdsa"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/crypto"
	"github.com/ethereum/go-ethereum/common"
)

var (
	key0, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	key1, _ = crypto.HexToECDSA("8a1f9a8f95be41cd7ccb6168179afb4504aefe388d1e14474d32c45c72ce7b7a")
	key2, _ = crypto.HexToECDSA("49a7b37aa6f6645917e7b807e9d1c00d4fa71f18343b0d4122a4d2df64dd6fee")
	addr0   = crypto.PubkeyToAddress(key0.PublicKey)
	addr1   = crypto.PubkeyToAddress(key1.PublicKey)
	addr2   = crypto.PubkeyToAddress(key2.PublicKey)
)

func newTestBackend() *backends.SimulatedBackend {
	return backends.NewSimulatedBackend(core.GenesisAlloc{
		addr0: {Balance: big.NewInt(1000000000)},
		addr1: {Balance: big.NewInt(1000000000)},
		addr2: {Balance: big.NewInt(1000000000)},
	})
}

func deploy(prvKey *ecdsa.PrivateKey, cpuDifficulty, memoryDifficulty uint64, backend *backends.SimulatedBackend) (common.Address, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	addr, _, _, err := DeployAdmission(deployTransactor, backend, new(big.Int).SetUint64(cpuDifficulty), new(big.Int).SetUint64(memoryDifficulty))
	if err != nil {
		return common.Address{}, err
	}
	backend.Commit()
	return addr, nil
}

func TestVerifyCPU(t *testing.T) {
	backend := newTestBackend()
	addr0, err := deploy(key0, 15, 15, backend)
	if err != nil {
		t.Fatalf("deploy contract: expected no error, got %v", err)
	}

	instance, err := NewAdmission(addr0, backend)
	if err != nil {
		t.Fatalf("expected no error, got %v", err)
	}

	ok, err := instance.VerifyCPU(nil, 5, new(big.Int).SetUint64(1))
	if err != nil {
		t.Fatalf("expected no error, got %v", err)
	}

	if ok {
		t.Fatalf("expected ok, got not ok")
	}

}

func TestVerifyMemory(t *testing.T) {
	backend := newTestBackend()
	addr0, err := deploy(key0, 15, 15, backend)
	if err != nil {
		t.Fatalf("deploy contract: expected no error, got %v", err)
	}

	instance, err := NewAdmission(addr0, backend)
	if err != nil {
		t.Fatalf("expected no error, got %v", err)
	}

	ok, err := instance.VerifyMemory(nil, 5, new(big.Int).SetUint64(1))
	if err != nil {
		t.Fatalf("expected no error, got %v", err)
	}

	if !ok {
		t.Fatalf("expected %v, got not %v", true, ok)
	}
}

func TestUpdateCPUDifficulty(t *testing.T) {
	defaultDifficulty := uint64(5)
	newCPUDifficulty := uint64(15)

	backend := newTestBackend()
	addr0, err := deploy(key0, defaultDifficulty, defaultDifficulty, backend)
	if err != nil {
		t.Fatalf("deploy contract: expected no error, got %v", err)
	}

	instance, err := NewAdmission(addr0, backend)
	if err != nil {
		t.Fatalf("expected no error, got %v", err)
	}

	auth := bind.NewKeyedTransactor(key0)

	_, err = instance.UpdateCPUDifficulty(auth, new(big.Int).SetUint64(newCPUDifficulty))
	if err != nil {
		t.Fatalf("expected no error, got %v", err)
	}

	backend.Commit()

	v, err := instance.CpuDifficulty(nil)
	if err != nil {
		t.Fatalf("expected no error, got %v", err)
	}

	if v.Uint64() != newCPUDifficulty {
		t.Fatalf("expected %d, got %v", newCPUDifficulty, v.Uint64())
	}
}
