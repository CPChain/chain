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

package dpor

import (
	"context"
	"crypto/ecdsa"
	"fmt"

	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/contracts/dpor/contract"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/crypto"
)

var (
	key, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	addr   = crypto.PubkeyToAddress(key.PublicKey)
)

func deploy(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	deployTransactor.Value = amount
	addr, _, _, err := contract.DeployCampaign(deployTransactor, backend)
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
	campaign, err := NewCampaign(transactOpts, contractAddr, contractBackend)
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
	minimumNoc, err := campaign.MinimumNoc()
	checkError(t, "minimumNoc error: %v", err)
	fmt.Println("minimumNoc:", minimumNoc)

	// minimumRpt
	minimumRpt, err := campaign.MinimumRpt()
	checkError(t, "minimumRpt error: %v", err)
	fmt.Println("minimumRpt:", minimumRpt)
	contractBackend.Commit()

	// test contract map variable call.
	numOfCampaign, deposit, startViewIdx, err := campaign.CandidateInfoOf(addr)
	checkError(t, "CandidateInfoOf error: %v", err)
	fmt.Println("candidate info of", addr.Hex(), ":", numOfCampaign, deposit, startViewIdx)

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
	campaign, err := NewCampaign(transactOpts, contractAddr, contractBackend)
	checkError(t, "can't deploy root registry: %v", err)
	_ = contractAddr
	printBalance(contractBackend)

	// setup TransactOpts
	campaign.TransactOpts = *bind.NewKeyedTransactor(key)
	campaign.TransactOpts.Value = big.NewInt(50 * 1)

	// ClaimCampaign 1st time
	tx, err := campaign.ClaimCampaign(big.NewInt(1), big.NewInt(60))
	checkError(t, "ClaimCampaign error:", err)
	fmt.Println("ClaimCampaign tx:", tx.Hash().Hex())
	contractBackend.Commit()
	printBalance(contractBackend)

	// verify result
	numOfCampaign, deposit, startViewIdx, err := campaign.CandidateInfoOf(addr)
	checkError(t, "CandidateInfoOf error: %v", err)
	fmt.Println("candidate info of", addr.Hex(), ":", numOfCampaign, deposit, startViewIdx)
	assert(1, 50, numOfCampaign, deposit, t)

	tx, err = campaign.ClaimCampaign(big.NewInt(1), big.NewInt(60))
	checkError(t, "ClaimCampaign error: %v", err)
	fmt.Println("ClaimCampaign tx:", tx.Hash().Hex())
	contractBackend.Commit()
	printBalance(contractBackend)

	// test contract map variable call.
	numOfCampaign, deposit, startViewIdx, err = campaign.CandidateInfoOf(addr)
	checkError(t, "CandidateInfoOf error: %v", err)
	fmt.Println("candidate info of", addr.Hex(), ":", numOfCampaign, deposit, startViewIdx)
	assert(2, 100, numOfCampaign, deposit, t)

	// get candidates by view index
	candidates, err := campaign.CandidatesOf(big.NewInt(0))
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
	campaign, err := NewCampaign(transactOpts, contractAddr, contractBackend)
	checkError(t, "can't deploy root registry: %v", err)
	_ = contractAddr
	printBalance(contractBackend)

	// setup TransactOpts
	campaign.TransactOpts = *bind.NewKeyedTransactor(key)
	campaign.TransactOpts.Value = big.NewInt(50 * 2)

	tx, err := campaign.ClaimCampaign(big.NewInt(2), big.NewInt(60))
	checkError(t, "ClaimCampaign error:", err)
	fmt.Println("ClaimCampaign tx:", tx.Hash().Hex())
	contractBackend.Commit()
	printBalance(contractBackend)

	// test contract map variable call.
	numOfCampaign, deposit, startViewIdx, err := campaign.CandidateInfoOf(addr)
	checkError(t, "CandidateInfoOf error: %v", err)
	fmt.Println("candidate info of", addr.Hex(), ":", numOfCampaign, deposit, startViewIdx)
	assert(2, 100, numOfCampaign, deposit, t)

	// get candidates by view index
	verifyCandidates(campaign, t, big.NewInt(0), 1)
	printBalance(contractBackend)
	contractBackend.Commit()

	// view change 1st time
	fmt.Println("ViewChange")
	tx, err = campaign.ViewChange()
	checkError(t, "ViewChange error:%v", err)
	contractBackend.Commit()

	// get candidates by view index
	verifyCandidates(campaign, t, big.NewInt(0), 1)
	printBalance(contractBackend)

	// get candidates by view index
	verifyCandidates(campaign, t, big.NewInt(1), 1)
	printBalance(contractBackend)

	// view change 2nd time
	fmt.Println("ViewChange")
	tx, err = campaign.ViewChange()
	checkError(t, "ViewChange error:%v", err)
	contractBackend.Commit()

	// get candidates by view index
	verifyCandidates(campaign, t, big.NewInt(0), 1)
	verifyCandidates(campaign, t, big.NewInt(1), 1)
	verifyCandidates(campaign, t, big.NewInt(2), 0)
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

	verifyCandidates(campaign, t, big.NewInt(0), 1)
	verifyCandidates(campaign, t, big.NewInt(1), 1)
	verifyCandidates(campaign, t, big.NewInt(2), 0)
}

func verifyCandidates(campaign *Campaign, t *testing.T, viewIdx *big.Int, candidateLengh int) {
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

func assert(expectNum int64, expectDeposit int64, numOfCampaign *big.Int, deposit *big.Int, t *testing.T) {
	if numOfCampaign.Cmp(big.NewInt(expectNum)) != 0 || deposit.Cmp(big.NewInt(expectDeposit)) != 0 {
		t.Fatal("unexpected numOfCampaign, deposit:", numOfCampaign, deposit)
	}
}
