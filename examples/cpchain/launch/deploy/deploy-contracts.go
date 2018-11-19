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

package main

import (
	"bytes"
	"context"
	"crypto/ecdsa"
	"fmt"
	"log"
	"math/big"
	"os"
	"path/filepath"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/admission"
	campaign "bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"
	signerRegister "bitbucket.org/cpchain/chain/contracts/dpor/contracts/signer_register"
	"bitbucket.org/cpchain/chain/contracts/pdash/sol"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	endPoint         = "http://localhost:8501"
	keyStoreFilePath = "./data/data1/keystore/"
)

func deploySigner() {

	// Create client.
	client, err := cpclient.Dial(endPoint)
	if err != nil {
		log.Fatal(err.Error())
	}

	// Open keystore file.
	file, err := os.Open(keyStoreFilePath)
	if err != nil {
		log.Fatal(err.Error())
	}

	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	if err != nil {
		log.Fatal(err.Error())
	}

	// Create keystore and get account.
	kst := keystore.NewKeyStore(keyPath, 2, 1)
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, "password")
	if err != nil {
		log.Fatal(err.Error())
	}

	// Get private and public keys.
	privateKey := key.PrivateKey
	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		log.Fatal("error casting public key to ECDSA")
	}

	// Get address.
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	fmt.Println("from address:", fromAddress.Hex()) // 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a

	// Check balance.
	bal, err := client.BalanceAt(context.Background(), fromAddress, nil)
	fmt.Println("balance:", bal)

	// Get gas price.
	gasPrice, err := client.SuggestGasPrice(context.Background())
	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("gasPrice:", gasPrice)

	// Set gas limit.
	gasLimit := 3000000

	// Setup transaction auth.
	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(0)       // in wei
	auth.GasLimit = uint64(gasLimit) // in units
	auth.GasPrice = gasPrice

	// Launch contract deploy transaction.
	address, tx, _, err := signerRegister.DeploySignerConnectionRegister(auth, client)
	if err != nil {
		log.Fatal(err.Error())
	}

	fmt.Println("Contract address: ", address.Hex())
	fmt.Println("Transaction hash: ", tx.Hash().Hex())

	// Record time cost.
	startTime := time.Now()
	fmt.Printf("TX start @:%s", time.Now())

	// Wait for deploy.
	ctx := context.Background()
	addressAfterMined, err := bind.WaitDeployed(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))

	if !bytes.Equal(address.Bytes(), addressAfterMined.Bytes()) {
		log.Fatalf("mined address :%s,before mined address:%s", addressAfterMined, address)
	}
}

func deployCampaign() {

	// Create client.
	client, err := cpclient.Dial(endPoint)
	if err != nil {
		log.Fatal(err.Error())
	}

	// Open keystore file.
	file, err := os.Open(keyStoreFilePath)
	if err != nil {
		log.Fatal(err.Error())
	}

	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	if err != nil {
		log.Fatal(err.Error())
	}

	// Create keystore and get account.
	kst := keystore.NewKeyStore(keyPath, 2, 1)
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, "password")
	if err != nil {
		log.Fatal(err.Error())
	}

	// Get private and public keys.
	privateKey := key.PrivateKey
	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		log.Fatal("error casting public key to ECDSA")
	}

	// Get address.
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	fmt.Println("from address:", fromAddress.Hex()) // 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a

	// Check balance.
	bal, err := client.BalanceAt(context.Background(), fromAddress, nil)
	fmt.Println("balance:", bal)

	// Get gas price.
	gasPrice, err := client.SuggestGasPrice(context.Background())
	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("gasPrice:", gasPrice)

	// Set gas limit.
	gasLimit := 3000000

	// Setup transaction auth.
	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(0)       // in wei
	auth.GasLimit = uint64(gasLimit) // in units
	auth.GasPrice = gasPrice

	// Launch contract deploy transaction.
	acAddr, _, _, err := admission.DeployAdmission(auth, client, big.NewInt(50), big.NewInt(50))
	if err != nil {
		log.Fatal(err.Error())
	}

	address, tx, _, err := campaign.DeployCampaign(auth, client, acAddr)
	if err != nil {
		log.Fatal(err.Error())
	}

	fmt.Println("Contract address: ", address.Hex())
	fmt.Println("Transaction hash: ", tx.Hash().Hex())

	// Record time cost.
	startTime := time.Now()
	fmt.Printf("TX start @:%s", time.Now())

	// Wait for deploy.
	ctx := context.Background()
	addressAfterMined, err := bind.WaitDeployed(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))

	if !bytes.Equal(address.Bytes(), addressAfterMined.Bytes()) {
		log.Fatalf("mined address :%s,before mined address:%s", addressAfterMined, address)
	}
}

func deployRegister() {
	// Create client.
	client, err := cpclient.Dial(endPoint)
	if err != nil {
		log.Fatal(err)
	}

	// Open keystore file.
	file, err := os.Open(keyStoreFilePath)
	if err != nil {
		log.Fatal(err)
	}

	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	if err != nil {
		log.Fatal(err)
	}

	// Create keystore and get account.
	kst := keystore.NewKeyStore(keyPath, 2, 1)
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, "password")
	if err != nil {
		log.Fatal(err)
	}

	// Get private and public keys.
	privateKey := key.PrivateKey
	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		log.Fatal("error casting public key to ECDSA")
	}

	// Get address.
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	fmt.Println("from address:", fromAddress.Hex()) // 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a

	// Check balance.
	bal, err := client.BalanceAt(context.Background(), fromAddress, nil)
	fmt.Println("balance:", bal)

	// Get gas price.
	gasPrice, err := client.SuggestGasPrice(context.Background())
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("gasPrice:", gasPrice)

	// Set gas limit.
	gasLimit := 3000000

	// Setup transaction auth.
	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(0)       // in wei
	auth.GasLimit = uint64(gasLimit) // in units
	auth.GasPrice = gasPrice

	// Launch contract deploy transaction.
	address, tx, _, err := pdash.DeployRegister(auth, client)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println("Contract address: ", address.Hex())
	fmt.Println("Transaction hash: ", tx.Hash().Hex())

	// Record time cost.
	startTime := time.Now()
	fmt.Printf("TX start @:%s", time.Now())

	// Wait for deploy.
	ctx := context.Background()
	addressAfterMined, err := bind.WaitDeployed(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))

	if !bytes.Equal(address.Bytes(), addressAfterMined.Bytes()) {
		log.Fatalf("mined address :%s,before mined address:%s", addressAfterMined, address)
	}
}

func deployPdash() {
	// Create client.
	client, err := cpclient.Dial(endPoint)
	if err != nil {
		log.Fatal(err)
	}

	// Open keystore file.
	file, err := os.Open(keyStoreFilePath)
	if err != nil {
		log.Fatal(err)
	}

	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	if err != nil {
		log.Fatal(err)
	}

	// Create keystore and get account.
	kst := keystore.NewKeyStore(keyPath, 2, 1)
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, "password")
	if err != nil {
		log.Fatal(err)
	}

	// Get private and public keys.
	privateKey := key.PrivateKey
	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		log.Fatal("error casting public key to ECDSA")
	}

	// Get address.
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	fmt.Println("from address:", fromAddress.Hex()) // 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a

	// Check balance.
	bal, err := client.BalanceAt(context.Background(), fromAddress, nil)
	fmt.Println("balance:", bal)

	// Get gas price.
	gasPrice, err := client.SuggestGasPrice(context.Background())
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("gasPrice:", gasPrice)

	// Set gas limit.
	gasLimit := 3000000

	// Setup transaction auth.
	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(0)       // in wei
	auth.GasLimit = uint64(gasLimit) // in units
	auth.GasPrice = gasPrice

	// Launch contract deploy transaction.
	address, tx, _, err := pdash.DeployPdash(auth, client)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println("Contract address: ", address.Hex())
	fmt.Println("Transaction hash: ", tx.Hash().Hex())

	// Record time cost.
	startTime := time.Now()
	fmt.Printf("TX start @:%s", time.Now())

	// Wait for deploy.
	ctx := context.Background()
	addressAfterMined, err := bind.WaitDeployed(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))

	if !bytes.Equal(address.Bytes(), addressAfterMined.Bytes()) {
		log.Fatalf("mined address :%s,before mined address:%s", addressAfterMined, address)
	}
}
func main() {
	deployCampaign()
	deploySigner()
	deployPdash()
	deployRegister()
}
