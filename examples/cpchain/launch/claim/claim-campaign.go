package main

import (
	"context"
	"crypto/ecdsa"
	"encoding/hex"
	"fmt"
	"log"
	"math/big"
	"os"
	"path/filepath"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/accounts/rsakey"
	campaign "bitbucket.org/cpchain/chain/contracts/dpor/contract/campaign"
	signerRegister "bitbucket.org/cpchain/chain/contracts/dpor/contract/signerRegister"
	"bitbucket.org/cpchain/chain/crypto"
	"bitbucket.org/cpchain/chain/ethclient"
	"github.com/ethereum/go-ethereum/common"
)

type keystorePair struct {
	keystorePath   string
	passphrase     string
	rsaPubkeyPath  string
	rsaPrivKeyPath string
}

var (
	endPoint  = "http://localhost:8501"
	dataDir   = "./data/"
	keystores = []keystorePair{
		{
			"dd1/keystore/",
			"password",
			"dd1/rsa/rsa_pub.pem",
			"dd1/rsa/rsa_pri.pem",
		},
		{
			"dd2/keystore/",
			"password",
			"dd2/rsa/rsa_pub.pem",
			"dd2/rsa/rsa_pri.pem",
		},
		{
			"dd3/keystore/",
			"pwdnode1",
			"dd3/rsa/rsa_pub.pem",
			"dd3/rsa/rsa_pri.pem",
		},
		{
			"dd4/keystore/",
			"pwdnode2",
			"dd4/rsa/rsa_pub.pem",
			"dd4/rsa/rsa_pri.pem",
		},
		{
			"dd5/keystore/",
			"password",
			"dd5/rsa/rsa_pub.pem",
			"dd5/rsa/rsa_pri.pem",
		},
		{
			"dd6/keystore/",
			"password",
			"dd6/rsa/rsa_pub.pem",
			"dd6/rsa/rsa_pri.pem",
		},
		{
			"dd7/keystore/",
			"password",
			"dd7/rsa/rsa_pub.pem",
			"dd7/rsa/rsa_pri.pem",
		},
		{
			"dd8/keystore/",
			"password",
			"dd8/rsa/rsa_pub.pem",
			"dd8/rsa/rsa_pri.pem",
		},
		{
			"dd9/keystore/",
			"password",
			"dd9/rsa/rsa_pub.pem",
			"dd9/rsa/rsa_pri.pem",
		},
		{
			"dd10/keystore/",
			"password",
			"dd10/rsa/rsa_pub.pem",
			"dd10/rsa/rsa_pri.pem",
		},
	}
)

func getAccount(keyStoreFilePath string, passphrase string, rsaPubkeyPath string, rsaPrivkeyPath string) (*ecdsa.PrivateKey, *ecdsa.PublicKey, common.Address, []byte) {
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

	rsaKey, err := rsakey.NewRsaKey(dataDir)
	fmt.Println(err)

	return privateKey, publicKeyECDSA, fromAddress, rsaKey.PublicKey.RsaPublicKeyBytes
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

	instance, err := campaign.NewCampaign(contractAddress, client)

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

func claimSigner(privateKey *ecdsa.PrivateKey, publicKey *ecdsa.PublicKey, address common.Address, contractAddress common.Address, rsaPubkey []byte) {
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

	instance, err := signerRegister.NewSignerConnectionRegister(contractAddress, client)

	gasLimit := 3000000

	auth := bind.NewKeyedTransactor(privateKey)
	auth.GasLimit = uint64(gasLimit)
	auth.GasPrice = gasPrice
	auth.Value = big.NewInt(500)

	fmt.Println("rsaPubkey", hex.Dump(rsaPubkey))

	tx, err := instance.RegisterPublicKey(auth, rsaPubkey)
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

	pubkey, err := instance.GetPublicKey(nil, address)
	fmt.Println("pubkey of", address.Hex(), ":", pubkey)
}

func main() {

	campaignAddress := common.HexToAddress("0x1a9fAE75908752d0ABf4DCa45ebcaC311C376290")
	signerAddress := common.HexToAddress("0x4CE687F9dDd42F26ad580f435acD0dE39e8f9c9C")

	for i, kPair := range keystores {
		fmt.Println(i)
		keystoreFile, passphrase, rsaPubkeyPath, rsaPrivkeyPath := kPair.keystorePath, kPair.passphrase, kPair.rsaPubkeyPath, kPair.rsaPrivKeyPath
		privKey, pubKey, addr, rsaPubKey := getAccount(keystoreFile, passphrase, rsaPubkeyPath, rsaPrivkeyPath)
		claimCampaign(privKey, pubKey, addr, campaignAddress)
		claimSigner(privKey, pubKey, addr, signerAddress, rsaPubKey)
	}
}
