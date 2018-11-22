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

package deploy

import (
	"bytes"
	"context"
	"fmt"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

func printTx(tx *types.Transaction, err error, client *cpclient.Client, contractAddress common.Address) context.Context {
	ctx := context.Background()
	// fmt.Printf("Transaction: 0x%x\n", tx.Hash())
	// startTime := time.Now()
	// fmt.Printf("TX start @:%s", time.Now())
	addressAfterMined, err := bind.WaitDeployed(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	// fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	if !bytes.Equal(contractAddress.Bytes(), addressAfterMined.Bytes()) {
		log.Fatalf("mined contractAddress :%s,before mined contractAddress:%s", addressAfterMined, contractAddress)
	}
	return ctx
}

func printBalance(client *cpclient.Client, fromAddress common.Address) {
	// Check balance.
	bal, _ := client.BalanceAt(context.Background(), fromAddress, nil)
	fmt.Println("balance:", bal)
}

func PrintContract(address common.Address) {
	fmt.Println("================================================================")
	fmt.Printf("Contract Address: 0x%x\n", address)
	fmt.Println("================================================================")
}

func FormatPrint(msg string) {
	fmt.Println("\n\n================================================================")
	fmt.Println(msg)
	fmt.Println("================================================================")
}
