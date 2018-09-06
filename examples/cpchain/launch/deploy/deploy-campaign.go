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

	"github.com/ethereum/go-ethereum/accounts/abi/bind"
	"github.com/ethereum/go-ethereum/accounts/keystore"
	"github.com/ethereum/go-ethereum/contracts/dpor/contract"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/ethclient"
)

var (
	endPoint         = "http://localhost:8501"
	keyStoreFilePath = "../../data/dd1/keystore/"
)

func deployCampaign() {

	// Create client.
	client, err := ethclient.Dial(endPoint)
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
	fmt.Println("from address:", fromAddress.Hex()) // 0x96216849c49358B10257cb55b28eA603c874b05E

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
	address, tx, _, err := contract.DeployCampaign(auth, client)
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
}
