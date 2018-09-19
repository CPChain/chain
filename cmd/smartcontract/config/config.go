package config

import (
	"crypto/ecdsa"
	"fmt"
	"log"
	"os"
	"path/filepath"

	"github.com/ethereum/go-ethereum/accounts/keystore"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/ethclient"
)

var (
	endPoint         = "http://localhost:8501"
	keyStoreFilePath = "./examples/cpchain/data/dd1/keystore/"
)

func Connect() (*ethclient.Client, error, *ecdsa.PrivateKey, *ecdsa.PublicKey, common.Address) {
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

	// Get contractAddress.
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	fmt.Println("from contractAddress:", fromAddress.Hex()) // 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a

	return client, err, privateKey, publicKeyECDSA, fromAddress
}
