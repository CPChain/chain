package main

import (
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
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/contracts/dpor/contract"
	"bitbucket.org/cpchain/chain/crypto"
	"bitbucket.org/cpchain/chain/ethclient"
)

type keystorePair struct {
	keystorePath string
	passphrase   string
}

var (
	endPoint  = "http://localhost:8501"
	dataDir   = "./data/"
	keystores = []keystorePair{
		{
			"dd1/keystore/",
			"password",
		},
		{
			"dd2/keystore/",
			"password",
		},
		{
			"dd3/keystore/",
			"pwdnode1",
		},
	}
)

func getAccount(keyStoreFilePath string, passphrase string) (*ecdsa.PrivateKey, *ecdsa.PublicKey, common.Address) {
	// Load account.
	file, err := os.Open(dataDir + keyStoreFilePath)
	if err != nil {
		log.Fatal(err)
	}

	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	if err != nil {
		log.Fatal(err)
	}

	kst := keystore.NewKeyStore(keyPath, 2, 1)

	// Get account.
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, passphrase)
	if err != nil {
		log.Fatal(err)
	}

	privateKey := key.PrivateKey
	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		log.Fatal("error casting public key to ECDSA")
	}
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)

	return privateKey, publicKeyECDSA, fromAddress
}

func claimCampaign(privateKey *ecdsa.PrivateKey, publicKey *ecdsa.PublicKey, address common.Address, contractAddress common.Address) {
	// Create client.
	client, err := ethclient.Dial(endPoint)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("from address:", address.Hex()) // 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a

	// Check balance.
	bal, err := client.BalanceAt(context.Background(), address, nil)
	fmt.Println("balance:", bal)

	gasPrice, err := client.SuggestGasPrice(context.Background())
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("gasPrice:", gasPrice)

	startTime := time.Now()
	fmt.Printf("transaction start at: %s\n", time.Now())

	ctx := context.Background()

	instance, err := contract.NewCampaign(contractAddress, client)

	baseDeposit := 50
	gasLimit := 3000000
	numOfCampaign := 10
	myRpt := 60

	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(int64(baseDeposit * numOfCampaign))
	auth.GasLimit = uint64(gasLimit)
	auth.GasPrice = gasPrice

	tx, err := instance.ClaimCampaign(auth, big.NewInt(int64(numOfCampaign)), big.NewInt(int64(myRpt)))
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println("transaction hash: ", tx.Hash().Hex())

	startTime = time.Now()
	receipt, err := bind.WaitMined(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}

	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	fmt.Println("receipt.Status:", receipt.Status)

	noc, deposit, timestamp, err := instance.CandidateInfoOf(nil, address)
	fmt.Println("candidate info of", address.Hex(), ":", noc, deposit, timestamp)
}

func main() {

	contractAddress := common.HexToAddress("0x1a9fAE75908752d0ABf4DCa45ebcaC311C376290")

	for _, kPair := range keystores {
		keystoreFile, passphrase := kPair.keystorePath, kPair.passphrase
		privKey, pubKey, addr := getAccount(keystoreFile, passphrase)
		claimCampaign(privKey, pubKey, addr, contractAddress)
	}
}
