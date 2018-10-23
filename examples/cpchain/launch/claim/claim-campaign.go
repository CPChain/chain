package main

import (
	"context"
	"crypto/ecdsa"
	"encoding/hex"
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	campaign "bitbucket.org/cpchain/chain/contracts/dpor/contract/campaign"
	signerRegister "bitbucket.org/cpchain/chain/contracts/dpor/contract/signerRegister"
	"bitbucket.org/cpchain/chain/crypto"
	"bitbucket.org/cpchain/chain/ethclient"
	"github.com/ethereum/go-ethereum/common"
)

type keystorePair struct {
	keystorePath string
	passphrase   string
	rsaPath      string
}

var (
	endPoint  = "http://localhost:8501"
	dataDir   = "data/"
	keystores = []keystorePair{
		{
			"dd1/keystore/",
			"password",
			"dd1/rsa/",
		},
		{
			"dd2/keystore/",
			"password",
			"dd2/rsa/",
		},
		{
			"dd3/keystore/",
			"pwdnode1",
			"dd3/rsa/",
		},
		{
			"dd4/keystore/",
			"pwdnode2",
			"dd4/rsa/",
		},
		{
			"dd5/keystore/",
			"password",
			"dd5/rsa/",
		},
		{
			"dd6/keystore/",
			"password",
			"dd6/rsa/",
		},
		{
			"dd7/keystore/",
			"password",
			"dd7/rsa/",
		},
		{
			"dd8/keystore/",
			"password",
			"dd8/rsa/",
		},
		{
			"dd9/keystore/",
			"password",
			"dd9/rsa/",
		},
		{
			"dd10/keystore/",
			"password",
			"dd10/rsa/",
		},
	}
)

func getAccount(keyStoreFilePath string, passphrase string, rsaPath string) (*ecdsa.PrivateKey, *ecdsa.PublicKey, common.Address, []byte) {
	// Load account.
	ff, err := filepath.Abs(".")
	file, err := os.Open(ff + "/" + dataDir + keyStoreFilePath)
	if err != nil {
		log.Fatal(err.Error())
	}

	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	if err != nil {
		log.Fatal(err.Error())
	}

	kst := keystore.NewKeyStore(keyPath, 2, 1)

	// Get account.
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, passphrase)
	if err != nil {
		log.Fatal(err.Error())
	}

	privateKey := key.PrivateKey
	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		log.Fatal("error casting public key to ECDSA")
	}
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)

	rsaKey, err := rsakey.NewRsaKey(dataDir + rsaPath)
	fmt.Println(err)

	return privateKey, publicKeyECDSA, fromAddress, rsaKey.PublicKey.RsaPublicKeyBytes
}

func claimCampaign(privateKey *ecdsa.PrivateKey, publicKey *ecdsa.PublicKey, address common.Address, contractAddress common.Address) {
	// Create client.
	client, err := ethclient.Dial(endPoint)
	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("from address:", address.Hex()) // 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a

	// Check balance.
	bal, err := client.BalanceAt(context.Background(), address, nil)
	fmt.Println("balance:", bal)

	gasPrice, err := client.SuggestGasPrice(context.Background())
	if err != nil {
		log.Fatal(err.Error())
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
		log.Fatal(err.Error())
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
		log.Fatal(err.Error())
	}
	fmt.Println("from address:", address.Hex()) // 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a

	// Check balance.
	bal, err := client.BalanceAt(context.Background(), address, nil)
	fmt.Println("balance:", bal)

	gasPrice, err := client.SuggestGasPrice(context.Background())
	if err != nil {
		log.Fatal(err.Error())
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
		log.Fatal(err.Error())
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
		keystoreFile, passphrase, rsaPath := kPair.keystorePath, kPair.passphrase, kPair.rsaPath
		privKey, pubKey, addr, rsaPubKey := getAccount(keystoreFile, passphrase, rsaPath)
		claimCampaign(privKey, pubKey, addr, campaignAddress)
		claimSigner(privKey, pubKey, addr, signerAddress, rsaPubKey)
	}
}
