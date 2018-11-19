// Copyright 2016 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package dpor_test

import (
	"context"
	"crypto/ecdsa"
	"fmt"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	admission2 "bitbucket.org/cpchain/chain/admission"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/admission"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"
	"bitbucket.org/cpchain/chain/core"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	key, _      = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	addr        = crypto.PubkeyToAddress(key.PublicKey)
	numPerRound = 21
)

func deploy(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	acAddr, _, _, err := admission.DeployAdmission(deployTransactor, backend, big.NewInt(5), big.NewInt(5))
	addr, _, _, err := campaign.DeployCampaign(deployTransactor, backend, acAddr)
	if err != nil {
		return common.Address{}, err
	}
	backend.Commit()
	return addr, nil
}

func TestDeployCampaign(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	contractAddr, err := deploy(key, big.NewInt(0), contractBackend)
	checkError(t, "deploy contract: expected no error, got %v", err)

	transactOpts := bind.NewKeyedTransactor(key)
	campaign, err := dpor.NewCampaignWrapper(transactOpts, contractAddr, contractBackend)
	checkError(t, "can't deploy root registry: %v", err)
	_ = contractAddr
	contractBackend.Commit()

	//maximumNoc
	maximumNoc, err := campaign.MaximumNoc()
	checkError(t, "maximumNoc error: %v", err)
	fmt.Println("maximumNoc:", maximumNoc)

	//viewIdx
	viewIdx, err := campaign.ViewIdx()
	checkError(t, "viewIdx error: %v", err)
	fmt.Println("viewIdx:", viewIdx)

	//minimumNoc
	minimumNoc, err := campaign.MinNoc()
	checkError(t, "minimumNoc error: %v", err)
	fmt.Println("minimumNoc:", minimumNoc)

	// test contract map variable call.
	numOfCampaign, deposit, startViewIdx, endViewIdx, err := campaign.CandidateInfoOf(addr)
	checkError(t, "CandidateInfoOf error: %v", err)
	fmt.Println("candidate info of", addr.Hex(), ":", numOfCampaign, deposit, startViewIdx, endViewIdx)

	verifyCandidates(campaign, t, big.NewInt(0), 0)
}

func checkError(t *testing.T, msg string, err error) {
	if err != nil {
		t.Fatalf(msg, err)
	}
}

func TestClaimAndQuitCampaign(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	printBalance(contractBackend)

	fmt.Println("deploy Campaign")
	contractAddr, err := deploy(key, big.NewInt(0), contractBackend)
	fmt.Println("contractAddr:", contractAddr)
	checkError(t, "deploy contract: expected no error, got %v", err)
	contractBackend.Commit()
	printBalance(contractBackend)

	fmt.Println("load Campaign")
	transactOpts := bind.NewKeyedTransactor(key)
	campaign, err := dpor.NewCampaignWrapper(transactOpts, contractAddr, contractBackend)
	checkError(t, "can't deploy root registry: %v", err)
	_ = contractAddr
	printBalance(contractBackend)

	// setup TransactOpts
	campaign.TransactOpts = *bind.NewKeyedTransactor(key)
	campaign.TransactOpts.Value = big.NewInt(50 * 1)

	// compute cpu&memory pow
	config := admission2.DefaultConfig
	config.CpuDifficulty = 5
	config.MemoryDifficulty = 5
	ac := admission2.NewAdmissionControl(contractBackend.Blockchain(), addr, config)
	ac.Campaign()
	<-ac.DoneCh() // wait for done
	results := ac.GetResult()
	cpuBlockNum := results[admission2.Cpu].BlockNumber
	cpuNonce := results[admission2.Cpu].Nonce
	memBlockNum := results[admission2.Memory].BlockNumber
	memNonce := results[admission2.Memory].Nonce

	// ClaimCampaign 1st time
	tx, err := campaign.ClaimCampaign(big.NewInt(1), cpuNonce, big.NewInt(cpuBlockNum), memNonce, big.NewInt(memBlockNum))
	checkError(t, "ClaimCampaign error:", err)
	fmt.Println("ClaimCampaign tx:", tx.Hash().Hex())
	contractBackend.Commit()
	printBalance(contractBackend)

	// verify result
	numOfCampaign, deposit, startViewIdx, endViewIdx, err := campaign.CandidateInfoOf(addr)
	checkError(t, "CandidateInfoOf error: %v", err)
	fmt.Println("candidate info of", addr.Hex(), ":", numOfCampaign, deposit, startViewIdx, endViewIdx)
	assertCampaign(1, 50, numOfCampaign, deposit, t)

	tx, err = campaign.ClaimCampaign(big.NewInt(1), cpuNonce, big.NewInt(cpuBlockNum), memNonce, big.NewInt(memBlockNum))
	checkError(t, "ClaimCampaign error: %v", err)
	fmt.Println("ClaimCampaign tx:", tx.Hash().Hex())
	contractBackend.Commit()
	printBalance(contractBackend)

	// test contract map variable call.
	numOfCampaign, deposit, startViewIdx, endViewIdx, err = campaign.CandidateInfoOf(addr)
	checkError(t, "CandidateInfoOf error: %v", err)
	fmt.Println("candidate info of", addr.Hex(), ":", numOfCampaign, deposit, startViewIdx, endViewIdx)
	assertCampaign(2, 100, numOfCampaign, deposit, t)

	// get candidates by view index
	candidates, err := campaign.CandidatesOf(startViewIdx)
	checkError(t, "CandidatesOf error: %v", err)
	fmt.Println("len(candidates):", len(candidates))
	if len(candidates) != 1 {
		t.Fatal("len(candidates) != 1")
	}
	fmt.Println("candidates of first view:")
	for i := 0; i < len(candidates); i++ {
		fmt.Println("number", i, candidates[i].Hex())
	}
	printBalance(contractBackend)

	// quit campaign
	// setup TransactOpts
	campaign.TransactOpts = *bind.NewKeyedTransactor(key)
	campaign.TransactOpts.Value = big.NewInt(0)
	campaign.TransactOpts.GasLimit = 100000
	campaign.TransactOpts.GasPrice = big.NewInt(0)
	tx, err = campaign.QuitCampaign()
	checkError(t, "QuitCampaign error: %v", err)
	fmt.Println("QuitCampaign tx:", tx.Hash().Hex())
	contractBackend.Commit()
	printBalance(contractBackend)

	// verify quit campaign result
	candidates, err = campaign.CandidatesOf(big.NewInt(0))
	checkError(t, "CandidatesOf error: %v", err)
	fmt.Println("len(candidates):", len(candidates))
	if len(candidates) != 0 {
		t.Fatal("len(candidates) != 0")
	}
}

func TestClaimWhenDepositLessThanBase(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(100000000000000)}})
	printBalance(contractBackend)

	fmt.Println("deploy Campaign")
	contractAddr, err := deploy(key, big.NewInt(0), contractBackend)
	fmt.Println("contractAddr:", contractAddr)
	checkError(t, "deploy contract: expected no error, got %v", err)
	contractBackend.Commit()
	printBalance(contractBackend)

	fmt.Println("load Campaign")
	transactOpts := bind.NewKeyedTransactor(key)
	campaign, err := dpor.NewCampaignWrapper(transactOpts, contractAddr, contractBackend)
	checkError(t, "can't deploy root registry: %v", err)
	_ = contractAddr
	printBalance(contractBackend)

	// setup TransactOpts
	campaign.TransactOpts = *bind.NewKeyedTransactor(key)
	campaign.TransactOpts.Value = big.NewInt(40)
	campaign.TransactOpts.GasLimit = 1000000

	// compute cpu&memory pow
	config := admission2.DefaultConfig
	config.CpuDifficulty = 5
	config.MemoryDifficulty = 5
	ac := admission2.NewAdmissionControl(contractBackend.Blockchain(), addr, config)
	ac.Campaign()
	<-ac.DoneCh() // wait for done
	results := ac.GetResult()
	cpuBlockNum := results[admission2.Cpu].BlockNumber
	cpuNonce := results[admission2.Cpu].Nonce
	memBlockNum := results[admission2.Memory].BlockNumber
	memNonce := results[admission2.Memory].Nonce

	tx, err := campaign.ClaimCampaign(big.NewInt(2), cpuNonce, big.NewInt(cpuBlockNum), memNonce, big.NewInt(memBlockNum))
	fmt.Println(tx)
	checkError(t, "ClaimCampaign error:", err)

	// wait for view change
	verifyDeposit(campaign, t, big.NewInt(0))
	waitForViewChange(contractBackend, 2)

	// view change 1st time
	fmt.Println("ViewChange")
	tx, err = campaign.ViewChange()
	checkError(t, "ViewChange error:%v", err)
	contractBackend.Commit()

	// get candidates by start view index
	verifyCandidates(campaign, t, big.NewInt(1), 0)
	verifyDeposit(campaign, t, big.NewInt(0))
	printBalance(contractBackend)

}

func TestClaimAndViewChangeThenQuitCampaign(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(100000000000000)}})
	printBalance(contractBackend)

	fmt.Println("deploy Campaign")
	contractAddr, err := deploy(key, big.NewInt(0), contractBackend)
	fmt.Println("contractAddr:", contractAddr)
	checkError(t, "deploy contract: expected no error, got %v", err)
	contractBackend.Commit()
	printBalance(contractBackend)

	fmt.Println("load Campaign")
	transactOpts := bind.NewKeyedTransactor(key)
	campaign, err := dpor.NewCampaignWrapper(transactOpts, contractAddr, contractBackend)
	checkError(t, "can't deploy root registry: %v", err)
	_ = contractAddr
	printBalance(contractBackend)

	// setup TransactOpts
	campaign.TransactOpts = *bind.NewKeyedTransactor(key)
	campaign.TransactOpts.Value = big.NewInt(50 * 2)
	campaign.TransactOpts.GasLimit = 1000000

	// compute cpu&memory pow
	config := admission2.DefaultConfig
	config.CpuDifficulty = 5
	config.MemoryDifficulty = 5
	ac := admission2.NewAdmissionControl(contractBackend.Blockchain(), addr, config)
	ac.Campaign()
	<-ac.DoneCh() // wait for done
	results := ac.GetResult()
	cpuBlockNum := results[admission2.Cpu].BlockNumber
	cpuNonce := results[admission2.Cpu].Nonce
	memBlockNum := results[admission2.Memory].BlockNumber
	memNonce := results[admission2.Memory].Nonce

	tx, err := campaign.ClaimCampaign(big.NewInt(2), cpuNonce, big.NewInt(cpuBlockNum), memNonce, big.NewInt(memBlockNum))
	checkError(t, "ClaimCampaign error:", err)
	fmt.Println("ClaimCampaign tx:", tx.Hash().Hex())
	contractBackend.Commit()
	printBalance(contractBackend)

	// test contract map variable call.
	numOfCampaign, deposit, startViewIdx, endViewIdx, err := campaign.CandidateInfoOf(addr)
	checkError(t, "CandidateInfoOf error: %v", err)
	fmt.Println("candidate info of", addr.Hex(), ":", numOfCampaign, deposit, startViewIdx, endViewIdx)
	assertCampaign(2, 100, numOfCampaign, deposit, t)

	// get candidates by view index
	verifyCandidates(campaign, t, startViewIdx, 1)
	printBalance(contractBackend)
	contractBackend.Commit()

	// wait for view change
	verifyDeposit(campaign, t, big.NewInt(100))
	waitForViewChange(contractBackend, 2)

	// view change 1st time
	fmt.Println("ViewChange")
	tx, err = campaign.ViewChange()
	checkError(t, "ViewChange error:%v", err)
	contractBackend.Commit()

	// get candidates by start view index
	verifyCandidates(campaign, t, startViewIdx, 1)
	verifyDeposit(campaign, t, big.NewInt(50))
	printBalance(contractBackend)

	// view change 2nd time
	waitForViewChange(contractBackend, 1)
	fmt.Println("ViewChange")
	tx, err = campaign.ViewChange()
	checkError(t, "ViewChange error:%v", err)
	contractBackend.Commit()

	// get candidates by end view index
	verifyCandidates(campaign, t, endViewIdx, 0)
	verifyDeposit(campaign, t, big.NewInt(50))
	printBalance(contractBackend)

	// get candidates by view index
	verifyCandidates(campaign, t, big.NewInt(1), 1)
	verifyCandidates(campaign, t, big.NewInt(2), 1)
	verifyCandidates(campaign, t, big.NewInt(3), 0)
	printBalance(contractBackend)

	// quit campaign
	// setup TransactOpts
	campaign.TransactOpts = *bind.NewKeyedTransactor(key)
	campaign.TransactOpts.Value = big.NewInt(0)
	campaign.TransactOpts.GasLimit = 100000
	campaign.TransactOpts.GasPrice = big.NewInt(0)
	tx, err = campaign.QuitCampaign()
	checkError(t, "QuitCampaign error: %v", err)
	fmt.Println("QuitCampaign tx:", tx.Hash().Hex())
	contractBackend.Commit()
	printBalance(contractBackend)

	verifyCandidates(campaign, t, big.NewInt(1), 1)
	verifyCandidates(campaign, t, big.NewInt(2), 1)
	verifyCandidates(campaign, t, big.NewInt(3), 0)
}

func waitForViewChange(contractBackend *backends.SimulatedBackend, viewIdx int) {
	i := 0
	for i < viewIdx*numPerRound {
		contractBackend.Commit()
		i++
	}
}

func verifyDeposit(campaign *dpor.CampaignWrapper, t *testing.T, amount *big.Int) {
	_, deposit, _, _, _ := campaign.CandidateInfoOf(addr)
	if deposit.Cmp(amount) != 0 {
		t.Fatal("Deposit ", deposit, " != ", amount)
	}
}

func verifyCandidates(campaign *dpor.CampaignWrapper, t *testing.T, viewIdx *big.Int, candidateLengh int) {
	candidates, err := campaign.CandidatesOf(viewIdx)
	checkError(t, "CandidatesOf error: %v", err)
	fmt.Println("len(candidates):", len(candidates))
	if len(candidates) != candidateLengh {
		t.Fatal("len(candidates) != ", candidateLengh)
	}
}

func printBalance(contractBackend *backends.SimulatedBackend) {
	addrBalance, _ := contractBackend.BalanceAt(context.Background(), addr, nil)
	fmt.Println("==== addrBalance ==== ", addrBalance)
}

func assertCampaign(expectNum int64, expectDeposit int64, numOfCampaign *big.Int, deposit *big.Int, t *testing.T) {
	if numOfCampaign.Cmp(big.NewInt(expectNum)) != 0 || deposit.Cmp(big.NewInt(expectDeposit)) != 0 {
		t.Fatal("unexpected numOfCampaign, deposit:", numOfCampaign, deposit)
	}
}
