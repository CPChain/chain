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

package cpclient_test

import (
	"context"
	"fmt"
	"log"
	"math/big"
	"testing"

	cpchain "bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"github.com/ethereum/go-ethereum/common"
)

// Verify that Client implements the ethereum interfaces.
var (
	_ = cpchain.ChainReader(&cpclient.Client{})
	_ = cpchain.TransactionReader(&cpclient.Client{})
	_ = cpchain.ChainStateReader(&cpclient.Client{})
	_ = cpchain.ChainSyncReader(&cpclient.Client{})
	_ = cpchain.ContractCaller(&cpclient.Client{})
	_ = cpchain.GasEstimator(&cpclient.Client{})
	_ = cpchain.GasPricer(&cpclient.Client{})
	_ = cpchain.LogFilterer(&cpclient.Client{})
	_ = cpchain.PendingStateReader(&cpclient.Client{})
	// _ = ethereum.PendingStateEventer(&Client{})
	_ = cpchain.PendingContractCaller(&cpclient.Client{})
)

func TestGetRNodes(t *testing.T) {
	t.Skip("must start chain to test")
	client, err := cpclient.Dial("http://localhost:8501")
	// local
	if err != nil {
		log.Fatal(err.Error())
	}
	rnodes, err := client.GetRNodes(context.Background())
	fmt.Println(rnodes, err)
	fmt.Println("rpt is :", "addr", rnodes[0].Address, "rpt", rnodes[0].Rpt, "status", rnodes[0].Status)

	if rnodes[0].Rpt == 0 {
		t.Errorf("GetRNodes failed")
	}
}

func TestGetCurrentTerm(t *testing.T) {
	t.Skip("must start chain to test")
	client, err := cpclient.Dial("http://localhost:8501")
	if err != nil {
		log.Fatal(err.Error())
	}
	currentTerm, err := client.GetCurrentTerm(context.Background())
	fmt.Println("currentTerm", currentTerm)

	if err != nil {
		t.Errorf("GetCurrentTerm failed")
	}
}

func TestGetCurrentView(t *testing.T) {
	t.Skip("must start chain to test")
	client, err := cpclient.Dial("http://localhost:8501")
	// local
	if err != nil {
		log.Fatal(err.Error())
	}
	currentView, err := client.GetCurrentView(context.Background())
	fmt.Println("currentTerm", currentView)

	if err != nil {
		t.Errorf("GetCurrentView failed")
	}
}

func TestGetBlockGenerationInfoList(t *testing.T) {
	t.Skip("must start chain to test")
	client, err := cpclient.Dial("http://localhost:8501")
	// local
	if err != nil {
		log.Fatal(err.Error())
	}
	blockGenInfo, err := client.GetBlockGenerationInfo(context.Background())
	fmt.Println("committee is:", blockGenInfo, len(blockGenInfo.Proposers))
	fmt.Println("blockGenInfo ", "View:", blockGenInfo.View, "Term :", blockGenInfo.Term, "BlockNumber :", blockGenInfo.BlockNumber, "Proposer", blockGenInfo.Proposer, "Porposers", blockGenInfo.Proposers)
	if len(blockGenInfo.Proposers) != 4 {
		t.Errorf("GetBlockGenerationInfoList failed")
	}
}

func TestGetCommitteeNumber(t *testing.T) {
	t.Skip("must start chain to test")
	client, err := cpclient.Dial("http://localhost:8501")
	if err != nil {
		log.Fatal(err.Error())
	}
	committeesNum, err := client.GetCommitteeNumber(context.Background())
	fmt.Println("committees is :", committeesNum)

	if committeesNum != 4 {
		t.Errorf("GetCommittee failed")
	}
}

func TestClient_BlockByNumber(t *testing.T) {
	t.Skip("must start chain to test")
	client, err := cpclient.Dial("http://localhost:8501")
	// local
	if err != nil {
		log.Fatal(err.Error())
	}
	block, err := client.BlockByNumber(context.Background(), big.NewInt(138))
	if err != nil {
		log.Fatal("BlockByNumber is error: ", err)
	}
	Number := block.Number()
	tx := block.Transactions()
	fmt.Println("block Transactions is :", tx)
	fmt.Println("the blcok number is :", Number)

}

func TestClient_ChainConfig(t *testing.T) {
	t.Skip("must start chain to test")
	client, err := cpclient.Dial("http://localhost:8501")
	// local
	if err != nil {
		log.Fatal(err.Error())
	}
	cfg, err := client.ChainConfig()
	if err != nil {
		t.Fatal(err)
	}

	t.Log("chain config", "viewLen", cfg.Dpor.ViewLen, "termLen", cfg.Dpor.TermLen)
}

func TestGetProposerByBlock(t *testing.T) {
	t.Skip("must start chain to test")
	client, err := cpclient.Dial("http://localhost:8501")
	// local
	if err != nil {
		log.Fatal(err.Error())
	}
	cfg, err := client.GetProposerByBlock(context.Background(), big.NewInt(1))
	if err != nil {
		t.Fatal(err)
	}
	if cfg != common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092") {
		t.Fatal("wrong Proposer ", "we want ", common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092"), "we get ", cfg)
	}
}
