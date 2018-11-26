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
	t.Skip("skip test")
	fmt.Println("*******************************************************")
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
	t.Skip("skip test")
	fmt.Println("*******************************************************")
	client, err := cpclient.Dial("http://localhost:8501")
	if err != nil {
		log.Fatal(err.Error())
	}
	currentEpoch, err := client.GetCurrentTerm(context.Background())
	fmt.Println("currentEpoch", currentEpoch)

	if err != nil {
		t.Errorf("GetCurrentTerm failed")
	}
}

func TestGetCurrentView(t *testing.T) {
	t.Skip("skip test")
	fmt.Println("*******************************************************")
	client, err := cpclient.Dial("http://localhost:8501")
	// local
	if err != nil {
		log.Fatal(err.Error())
	}
	currentRound, err := client.GetCurrentView(context.Background())
	fmt.Println(currentRound)

	if err != nil {
		t.Errorf("GetCurrentView failed")
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
	committees, err := client.GetCommittees(context.Background())
	fmt.Println("committees is :", committees)

	if len(committees) < 1 {
		t.Errorf("GetCommittees failed")
	}
}
