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

package admission_test

import (
	"crypto/ecdsa"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/admission"
	"bitbucket.org/cpchain/chain/configs"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/admission"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/reward"
	"bitbucket.org/cpchain/chain/core"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	key0, _                  = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	key1, _                  = crypto.HexToECDSA("8a1f9a8f95be41cd7ccb6168179afb4504aefe388d1e14474d32c45c72ce7b7a")
	key2, _                  = crypto.HexToECDSA("49a7b37aa6f6645917e7b807e9d1c00d4fa71f18343b0d4122a4d2df64dd6fee")
	addr0                    = crypto.PubkeyToAddress(key0.PublicKey)
	addr1                    = crypto.PubkeyToAddress(key1.PublicKey)
	addr2                    = crypto.PubkeyToAddress(key2.PublicKey)
	cpuDifficulty     uint64 = 5
	memDifficulty     uint64 = 5
	cpuWorkTimeout    uint64 = 5
	memoryWorkTimeout uint64 = 5
)

func newTestBackend() *backends.SimulatedBackend {
	return backends.NewDporSimulatedBackend(core.GenesisAlloc{
		addr0: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		addr1: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		addr2: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
	})
}

func deployAdmission(prvKey *ecdsa.PrivateKey, cpuDifficulty, memoryDifficulty, cpuWorkTimeout, memoryWorkTimeout uint64, backend *backends.SimulatedBackend) (common.Address, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	acAddr, _, _, err := contract.DeployAdmission(deployTransactor, backend, new(big.Int).SetUint64(cpuDifficulty), new(big.Int).SetUint64(memoryDifficulty), new(big.Int).SetUint64(cpuWorkTimeout), new(big.Int).SetUint64(memoryWorkTimeout))
	if err != nil {
		return common.Address{}, err
	}
	backend.Commit()
	return acAddr, nil
}

func deployReward(prvKey *ecdsa.PrivateKey, backend *backends.SimulatedBackend) (common.Address, *reward.Reward, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	rewardAddr, _, rewardContract, err := reward.DeployReward(deployTransactor, backend)
	if err != nil {
		return common.Address{}, nil, err
	}
	backend.Commit()
	rewardContract.NewRaise(deployTransactor)
	rewardContract.SetPeriod(deployTransactor, big.NewInt(0))
	backend.Commit()
	return rewardAddr, rewardContract, nil
}

func deployCampaign(prvKey *ecdsa.PrivateKey, backend *backends.SimulatedBackend, admissionContract common.Address, rewardContract common.Address) (common.Address, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	campaignAddr, _, _, err := campaign.DeployCampaign(deployTransactor, backend, admissionContract, rewardContract)
	if err != nil {
		return common.Address{}, err
	}
	backend.Commit()
	return campaignAddr, nil
}

func deploy(prvKey *ecdsa.PrivateKey, cpuDifficulty, memoryDifficulty, cpuWorkTimeout, memoryWorkTimeout uint64, backend *backends.SimulatedBackend) (common.Address, common.Address, *reward.Reward, common.Address, error) {
	admissionAddr, err := deployAdmission(prvKey, cpuDifficulty, memoryDifficulty, cpuWorkTimeout, memoryWorkTimeout, backend)
	if err != nil {
		return common.Address{}, common.Address{}, nil, common.Address{}, err
	}

	rewardAddr, rewardContract, err := deployReward(prvKey, backend)
	if err != nil {
		return common.Address{}, common.Address{}, nil, common.Address{}, err
	}
	campaignAddr, err := deployCampaign(prvKey, backend, admissionAddr, rewardAddr)
	if err != nil {
		return common.Address{}, common.Address{}, nil, common.Address{}, err
	}
	return admissionAddr, rewardAddr, rewardContract, campaignAddr, nil
}

func TestVerifyCPU(t *testing.T) {
	backend := newTestBackend()
	acAddr, rewardAddr, rewardContract, campaignAddr, err := deploy(key0, cpuDifficulty, memDifficulty, cpuWorkTimeout, memoryWorkTimeout, backend)
	if err != nil {
		t.Fatalf("deploy contract: expected no error, got %v", err)
	}

	instance, err := contract.NewAdmission(acAddr, backend)
	if err != nil {
		t.Fatalf("expected no error, got %v", err)
	}

	cpuBlockNum, cpuNonce, _, _ := computeCorrectPow(key0, backend, addr0, acAddr, rewardAddr, rewardContract, campaignAddr)

	ok, err := instance.VerifyCPU(nil, addr0, cpuNonce, big.NewInt(cpuBlockNum), big.NewInt(int64(cpuDifficulty)))
	if err != nil {
		t.Fatalf("expected no error, got %v", err)
	}

	if !ok {
		t.Fatalf("expected ok, got not ok")
	}

}

func TestVerifyMemory(t *testing.T) {
	backend := newTestBackend()
	acAddr, rewardAddr, rewardContract, campaignAddr, err := deploy(key0, cpuDifficulty, memDifficulty, cpuWorkTimeout, memoryWorkTimeout, backend)
	if err != nil {
		t.Fatalf("deploy contract: expected no error, got %v", err)
	}

	instance, err := contract.NewAdmission(acAddr, backend)
	if err != nil {
		t.Fatalf("expected no error, got %v", err)
	}

	_, _, memBlockNum, memNonce := computeCorrectPow(key0, backend, addr0, acAddr, rewardAddr, rewardContract, campaignAddr)

	ok, err := instance.VerifyMemory(nil, addr0, memNonce, big.NewInt(memBlockNum), big.NewInt(int64(memDifficulty)))
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

	defaultTimeout := uint64(10)

	backend := newTestBackend()
	admissionAddr, _, _, _, err := deploy(key0, defaultDifficulty, defaultDifficulty, defaultTimeout, defaultTimeout, backend)
	if err != nil {
		t.Fatalf("deploy contract: expected no error, got %v", err)
	}

	instance, err := contract.NewAdmission(admissionAddr, backend)
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

	cd, md, ct, mt, err := instance.GetAdmissionParameters(nil)
	if err != nil {
		t.Fatal("GetDifficultyParameter is error ")
	}
	if cd.Uint64() != uint64(15) && md.Uint64() != uint64(5) && ct.Uint64() != uint64(10) && mt.Uint64() != uint64(10) {
		t.Fatal("error DifficultyParameter ", "we except", 15, 5, 10, 10, "the result", cd, md, ct, mt)
	}
}

func computeCorrectPow(prvKey *ecdsa.PrivateKey, contractBackend *backends.SimulatedBackend, addr common.Address, admissionAddr common.Address,
	rewardAddr common.Address, rewardContract *reward.Reward, campaignAddr common.Address) (cpuBlockNum int64, cpuNonce uint64, memBlockNum int64, memNonce uint64) {
	// compute cpu&memory pow
	ac := admission.NewAdmissionControl(contractBackend.Blockchain(), addr, admissionAddr, campaignAddr, rewardAddr)
	ac.SetSimulateBackend(contractBackend)
	ac.SetAdmissionKey(&keystore.Key{PrivateKey: prvKey})
	err := ac.FundForRNode()
	if err != nil {
		return
	}
	opts := bind.NewKeyedTransactor(prvKey)
	rewardContract.StartNewRound(opts)
	contractBackend.Commit()

	err = ac.Campaign(1)
	if err != nil {
		return
	}
	<-ac.DoneCh() // wait for done
	results := ac.GetResult()
	cpuBlockNum = results[admission.Cpu].BlockNumber
	cpuNonce = results[admission.Cpu].Nonce
	memBlockNum = results[admission.Memory].BlockNumber
	memNonce = results[admission.Memory].Nonce
	return
}
