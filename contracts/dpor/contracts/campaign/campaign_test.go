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

package campaign

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
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/admission"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

func TestCampaign(t *testing.T) {
	t.Skip("we shall use a simulated backend.")

	// create client.
	// client, err := cpchain.Dial("https://rinkeby.infura.io")
	client, err := cpclient.Dial("http://localhost:8501") // local
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
	fmt.Println("from address:", fromAddress.Hex()) // 0x96216849c49358B10257cb55b28eA603c874b05E

	bal, err := client.BalanceAt(context.Background(), fromAddress, nil)
	fmt.Println("bal:", bal)
	gasLimit := 3000000
	gasPrice, err := client.SuggestGasPrice(context.Background())
	fmt.Println("gasPrice:", gasPrice)
	if err != nil {
		log.Fatal(err.Error())
	}

	auth := bind.NewKeyedTransactor(privateKey)
	//auth.Nonce = big.NewInt(int64(nonce)) // not necessary
	auth.Value = big.NewInt(0)       // in wei
	auth.GasLimit = uint64(gasLimit) // in units
	auth.GasPrice = gasPrice

	// launch contract deploy transaction.
	acAddr, _, _, _ := admission.DeployAdmission(auth, client, big.NewInt(50), big.NewInt(50))
	address, tx, instance, err := DeployCampaign(auth, client, acAddr)
	if err != nil {
		log.Fatal(err.Error())
	}

	fmt.Printf("Contract pending deploy: 0x%x\n", address)
	fmt.Printf("Transaction waiting to be mined: 0x%x\n\n", tx.Hash())

	startTime := time.Now()
	fmt.Printf("TX start @:%s", time.Now())
	ctx := context.Background()
	addressAfterMined, err := bind.WaitDeployed(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	if !bytes.Equal(address.Bytes(), addressAfterMined.Bytes()) {
		log.Fatalf("mined address :%s,before mined address:%s", addressAfterMined, address)
	}

	fmt.Println("*******************************************************")
	numOfCampaign, deposit, _, _ := ClaimCampaign(privateKey, gasLimit, gasPrice, err, instance, startTime, ctx, client, fromAddress)
	assert(1, 50, numOfCampaign, deposit, t)

	fmt.Println("*******************************************************")
	numOfCampaign, deposit, _, _ = ClaimCampaign(privateKey, gasLimit, gasPrice, err, instance, startTime, ctx, client, fromAddress)
	assert(2, 100, numOfCampaign, deposit, t)
}

func assert(expectNum int64, expectDeposit int64, numOfCampaign *big.Int, deposit *big.Int, t *testing.T) {
	if numOfCampaign.Cmp(big.NewInt(expectNum)) != 0 || deposit.Cmp(big.NewInt(expectDeposit)) != 0 {
		t.Fatal("unexpected numOfCampaign, deposit:", numOfCampaign, deposit)
	}
}

func ClaimCampaign(privateKey *ecdsa.PrivateKey, gasLimit int, gasPrice *big.Int, err error, instance *Campaign, startTime time.Time,
	ctx context.Context, client *cpclient.Client, fromAddress common.Address) (*big.Int, *big.Int, *big.Int, *big.Int) {
	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(50)
	// in wei
	auth.GasLimit = uint64(gasLimit)
	// in units
	auth.GasPrice = gasPrice
	claimtx, err := instance.ClaimCampaign(auth, big.NewInt(int64(1)), 101, big.NewInt(123456), 101, big.NewInt(234567))
	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("TX:", claimtx.Hash().Hex())
	startTime = time.Now()
	receipt, err := bind.WaitMined(ctx, client, claimtx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	fmt.Println("receipt.Status:", receipt.Status)
	// test contract state variable call.
	x, err := instance.MinNoc(nil)
	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("minimum reputation: ", x)
	// test contract map variable call.
	numOfCampaign, deposit, startViewIdx, endViewIdx, err := instance.CandidateInfoOf(nil, fromAddress)
	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("candidate info of", fromAddress.Hex(), ":", numOfCampaign, deposit, startViewIdx, endViewIdx)
	// see candidates of view zero.
	candidates, err := instance.CandidatesOf(nil, big.NewInt(0))
	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("candidates of first view:")
	for i := 0; i < len(candidates); i++ {
		fmt.Println("number", i, candidates[i].Hex())
	}
	return numOfCampaign, deposit, startViewIdx, endViewIdx
}
