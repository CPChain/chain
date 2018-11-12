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
	"testing"

	"bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/api/cpclient"
)

// Verify that Client implements the ethereum interfaces.
var (
	_ = ethereum.ChainReader(&cpclient.Client{})
	_ = ethereum.TransactionReader(&cpclient.Client{})
	_ = ethereum.ChainStateReader(&cpclient.Client{})
	_ = ethereum.ChainSyncReader(&cpclient.Client{})
	_ = ethereum.ContractCaller(&cpclient.Client{})
	_ = ethereum.GasEstimator(&cpclient.Client{})
	_ = ethereum.GasPricer(&cpclient.Client{})
	_ = ethereum.LogFilterer(&cpclient.Client{})
	_ = ethereum.PendingStateReader(&cpclient.Client{})
	// _ = ethereum.PendingStateEventer(&Client{})
	_ = ethereum.PendingContractCaller(&cpclient.Client{})
)

func TestGetRNode(t *testing.T) {
	t.Skip("skip test")
	fmt.Println("*******************************************************")
	client, err := cpclient.Dial("http://localhost:8501")
	// local
	if err != nil {
		log.Fatal(err.Error())
	}
	rnodes, err := client.GetRNodes(context.Background())
	fmt.Println(rnodes)

	if len(rnodes) < 1 {
		t.Errorf("GetRNodes failed")
	}
}

func TestGetCurrentEpoch(t *testing.T) {
	t.Skip("skip test")
	fmt.Println("*******************************************************")
	client, err := cpclient.Dial("http://localhost:8501")
	if err != nil {
		log.Fatal(err.Error())
	}
	currentEpoch, err := client.GetCurrentEpoch(context.Background())
	fmt.Println(currentEpoch)

	if err != nil {
		t.Errorf("GetCurrentEpoch failed")
	}
}

func TestGetCurrentRound(t *testing.T) {
	t.Skip("skip test")
	fmt.Println("*******************************************************")
	client, err := cpclient.Dial("http://localhost:8501")
	// local
	if err != nil {
		log.Fatal(err.Error())
	}
	currentRound, err := client.GetCurrentRound(context.Background())
	fmt.Println(currentRound)

	if err != nil {
		t.Errorf("GetCurrentRound failed")
	}
}

func TestGetCommittees(t *testing.T) {
	t.Skip("skip test")
	fmt.Println("*******************************************************")
	client, err := cpclient.Dial("http://localhost:8501")
	// local
	if err != nil {
		log.Fatal(err.Error())
	}
	rnodes, err := client.GetCommittees(context.Background())
	fmt.Println(rnodes)

	if len(rnodes) < 1 {
		t.Errorf("GetCommittees failed")
	}
}
