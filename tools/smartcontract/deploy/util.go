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
	"crypto/ecdsa"
	"fmt"
	"math/big"
	"sync"

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
	_ = bal
	// fmt.Println("balance:", bal)
}

func PrintContract(title string, address common.Address) {
	fmt.Println("================================================================")
	fmt.Printf(title+" Contract Address: 0x%x\n", address)
	fmt.Println("================================================================")
}

func FormatPrint(msg string) {
	fmt.Println("\n\n================================================================")
	fmt.Println(msg)
	fmt.Println("================================================================")
}

type nonceCounter struct {
	nonce uint64
	lock  sync.RWMutex
}

var nonceInstance *nonceCounter
var once sync.Once
var needInit = true

func GetNonceInstance(init uint64) *nonceCounter {
	once.Do(func() {
		nonceInstance = &nonceCounter{nonce: init}
		needInit = false
	})
	return nonceInstance
}

func (p *nonceCounter) GetNonce() uint64 {
	p.lock.RLock()
	defer p.lock.RUnlock()
	orig := p.nonce
	p.nonce = p.nonce + 1
	return orig
}

func newAuth(client *cpclient.Client, privateKey *ecdsa.PrivateKey, fromAddress common.Address) *bind.TransactOpts {
	auth := bind.NewKeyedTransactor(privateKey)
	newNonce := uint64(0)

	if needInit {
		blockNumber := client.GetBlockNumber()

		initNonce, err := client.NonceAt(context.Background(), fromAddress, blockNumber)
		if err != nil {
			fmt.Println("get nonce failed", err)
		}
		GetNonceInstance(initNonce)
	}
	newNonce = GetNonceInstance(0).GetNonce()
	fmt.Println("newNonce:", newNonce)
	auth.Nonce = new(big.Int).SetUint64(newNonce)
	return auth

}

func newTransactor(privateKey *ecdsa.PrivateKey, nonce *big.Int) *bind.TransactOpts {
	auth := bind.NewKeyedTransactor(privateKey)
	if nonce.Cmp(big.NewInt(-1)) > 0 {
		auth.Nonce = nonce
	}
	return auth

}
