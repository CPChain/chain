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
	"context"
	"fmt"
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/proxy/proxy_contract"
	"bitbucket.org/cpchain/chain/tools/smartcontract/config"
	"github.com/ethereum/go-ethereum/common"
)

func ProxyContractRegister(password string) common.Address {
	client, err, privateKey, _, fromAddress := config.Connect(password)
	printBalance(client, fromAddress)
	// Launch contract deploy transaction.
	auth := newTransactor(privateKey, big.NewInt(0))
	contractAddress, tx, _, err := contract.DeployProxyContractRegister(auth, client)
	if err != nil {
		log.Fatal(err.Error(), "fromAddress", fromAddress.Hex(), "contractAddress:", contractAddress.Hex())
	}
	printTx(tx, err, client, contractAddress)
	return contractAddress
}

func DeployProxy(password string, nonce uint64) common.Address {
	client, err, privateKey, _, fromAddress := config.Connect(password)
	printBalance(client, fromAddress)
	// Launch contract deploy transaction.
	auth := newTransactor(privateKey, new(big.Int).SetUint64(nonce))
	contractAddress, tx, _, err := contract.DeployProxy(auth, client)
	if err != nil {
		log.Fatal(err.Error(), "fromAddress", fromAddress.Hex(), "contractAddress:", contractAddress.Hex())
	}
	printTx(tx, err, client, contractAddress)
	return contractAddress
}

func RegisterProxyAddress(title string, proxyContractAddress, realAddress common.Address, password string, nonce uint64, proxyNonce uint64) common.Address {
	proxyAddress := DeployProxy(password, nonce)
	success := UpdateRegisterProxyAddress(title, proxyContractAddress, proxyAddress, realAddress, password, new(big.Int).SetUint64(proxyNonce))
	if success {
		return proxyAddress
	} else {
		return common.Address{}
	}
}

func UpdateRegisterProxyAddress(title string, proxyContractAddress, proxyAddress, realAddress common.Address, password string, nonce *big.Int) bool {
	fmt.Println(title + " Register proxy contract proxy:" + proxyAddress.Hex() +
		" -> real:" + realAddress.Hex())
	client, err, privateKey, _, fromAddress := config.Connect(password)
	if err != nil {
		fmt.Println("failed")
		log.Fatal(err.Error(), "fromAddress", fromAddress, "proxyAddress", proxyAddress.Hex(), "realAddress:", realAddress.Hex())
		return false

	}
	printBalance(client, fromAddress)
	proxyContractRegister, _ := contract.NewProxyContractRegister(proxyContractAddress, client)
	auth := newTransactor(privateKey, nonce)
	auth.Value = big.NewInt(500)
	auth.GasLimit = 3000000
	gasPrice, err := client.SuggestGasPrice(context.Background())
	auth.GasPrice = gasPrice

	transaction, err := proxyContractRegister.RegisterProxyContract(auth, proxyAddress, realAddress)
	if err != nil {
		fmt.Println("failed")
		log.Fatal(err.Error(), "fromAddress", fromAddress, "proxyAddress", proxyAddress.Hex(), "realAddress:", realAddress.Hex())
		return false
	}
	receipt, err := bind.WaitMined(context.Background(), client, transaction)
	if err != nil {
		fmt.Println(title, "failed")
		log.Fatalf(title+" failed to deploy contact when mining :%v", err)
		return false
	}
	// fmt.Println("receipt.Status:", receipt.Status)
	if receipt.Status == 1 {
		fmt.Println(title, "success")
		return true
	} else {
		fmt.Println(title, "failed")
		return false
	}
}
