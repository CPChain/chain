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

package signer_register

import (
	"bytes"
	"context"
	"crypto/ecdsa"
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

func TestSignerRegister(t *testing.T) {
	t.Skip("we shall use a simulated backend.")

	client, privateKey, fromAddress, gasLimit, gasPrice, instance, ctx := deployContract()

	realAddress := "0x0bd6a2b982fc58e80a50beac02349871e2d016df"
	proxyAddress := "0x419a4dd52761c8272a700af72618e0e5e1ef3693"

	_ = proxyAddress
	_ = realAddress

	instance, _ = NewSignerConnectionRegister(common.HexToAddress(proxyAddress), client)

	fmt.Println("*******************************************************")
	registerSignerAndGet(t, privateKey, gasLimit, gasPrice, instance, ctx, client, fromAddress)
	fmt.Println("*******************************************************")
}

func deployContract() (*cpclient.Client, *ecdsa.PrivateKey, common.Address, int, *big.Int, *SignerConnectionRegister, context.Context) {
	// create client.
	// client, err := ethclient.Dial("https://rinkeby.infura.io")
	client, err := cpclient.Dial("http://localhost:8501")
	// local
	if err != nil {
		log.Fatal(err.Error())
	}
	// create account.
	// privateKey, err := crypto.HexToECDSA("fad9c8855b740a0b7ed4c221dbad0f33a83a49cad6b3fe8d5817ac83d38b6a19")
	file, _ := os.Open("../../../examples/cpchain/data/dd1/keystore/")
	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	kst := keystore.NewKeyStore(keyPath, 2, 1)
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, "password")
	privateKey := key.PrivateKey
	if err != nil {
		log.Fatal(err.Error())
	}
	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		log.Fatal("error casting public key to ECDSA")
	}
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	fmt.Println("from address:", fromAddress.Hex())
	// 0x96216849c49358B10257cb55b28eA603c874b05E
	bal, err := client.BalanceAt(context.Background(), fromAddress, nil)
	fmt.Println("bal:", bal)
	gasLimit := 3000000
	gasPrice, err := client.SuggestGasPrice(context.Background())
	fmt.Println("gasPrice:", gasPrice)
	if err != nil {
		log.Fatal(err.Error())
	}
	auth := bind.NewKeyedTransactor(privateKey)
	// auth.Nonce = big.NewInt(int64(nonce)) // not necessary
	auth.Value = big.NewInt(0)
	// in wei
	auth.GasLimit = uint64(gasLimit)
	// in units
	auth.GasPrice = gasPrice
	// launch contract deploy transaction.
	address, tx, instance, err := DeploySignerConnectionRegister(auth, client)
	if err != nil {
		log.Fatal(err.Error())
	}
	ctx := context.Background()
	receipt, err := bind.WaitMined(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Println("receipt.Status:", receipt.Status)
	fmt.Printf("Contract pending deploy: 0x%x\n", address)
	fmt.Printf("Transaction waiting to be mined: 0x%x\n\n", tx.Hash())
	startTime := time.Now()
	fmt.Printf("TX start @:%s", time.Now())
	addressAfterMined, err := bind.WaitDeployed(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	if !bytes.Equal(address.Bytes(), addressAfterMined.Bytes()) {
		log.Fatalf("mined address :%s,before mined address:%s", addressAfterMined, address)
	}
	return client, privateKey, fromAddress, gasLimit, gasPrice, instance, ctx
}

func registerSignerAndGet(t *testing.T, privateKey *ecdsa.PrivateKey, gasLimit int, gasPrice *big.Int, instance *SignerConnectionRegister, ctx context.Context, client *cpclient.Client, fromAddress common.Address) {
	// 1. load RsaPublicKey/PrivateKey
	fmt.Println("1.load RsaPublicKey/PrivateKey")

	rsaKey, err := rsakey.NewRsaKey("../testdata")

	// 2. register node2 public key on chain (claim campaign)
	fmt.Println("2.register node2 public key on chain")
	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(500)
	// in wei
	auth.GasLimit = uint64(gasLimit)
	// in units
	auth.GasPrice = gasPrice
	transaction, err := instance.RegisterPublicKey(auth, rsaKey.PublicKey.RsaPublicKeyBytes)
	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("TX:", transaction.Hash().Hex())
	startTime := time.Now()
	receipt, err := bind.WaitMined(ctx, client, transaction)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	fmt.Println("receipt.Status:", receipt.Status)

	// 3. node1 get public key with other's(node2) address
	fmt.Println("3.node1 get public key with other's(node2) address")
	publicKeyBytes, err := instance.GetPublicKey(nil, fromAddress)

	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("publicKeyBytes of", fromAddress.Hex(), ":", publicKeyBytes)

	// 4. node1 encrypt enode with node2's public key
	fmt.Println("4.node1 encrypt enode with node2's public key")

	enodeBytes := []byte("enode://abc:127.0.0.1:444")
	publicKeyFromChain, _ := rsakey.NewRsaPublicKey(publicKeyBytes)
	//if publicKey2 != publicKeyFromChain {
	//	t.Errorf("publicKey2 != publicKeyFromChain")
	//}
	encryptedEnodeBytes, err := publicKeyFromChain.RsaEncrypt(enodeBytes)
	fmt.Println("hex(encryptedEnodeBytes):", common.Bytes2Hex(encryptedEnodeBytes))

	// 5. node1 add encrypted enode(node2) on chain
	fmt.Println("5.node1 add encrypted enode(node2) on chain")

	auth = bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(500)
	// in wei
	auth.GasLimit = uint64(gasLimit)
	// in units
	auth.GasPrice = gasPrice
	transaction, err = instance.AddNodeInfo(auth, big.NewInt(1), fromAddress, encryptedEnodeBytes)

	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("TX:", transaction.Hash().Hex())
	startTime = time.Now()
	receipt, err = bind.WaitMined(ctx, client, transaction)
	if err != nil {
		log.Fatalf("failed to AddNodeInfo when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	fmt.Println("receipt.Status:", receipt.Status)

	// 6. node2 get enode from chain
	fmt.Println("6.node2 get enode from chain")
	rsaPublicKey, err := instance.GetNodeInfo(nil, big.NewInt(1), fromAddress)
	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("rsaPublicKey of", fromAddress.Hex(), ":", common.Bytes2Hex(rsaPublicKey))

	// 7. decrypt with node2 private key
	fmt.Println("7.decrypt with node2 private key")
	enode, err := rsaKey.RsaDecrypt(rsaPublicKey)

	fmt.Println("enode:", string(enode))

	if !bytes.Equal(enodeBytes, enode) {
		t.Errorf("expected enode:%v,got %v", enodeBytes, enode)
	}
}
