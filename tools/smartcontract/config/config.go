package config

import (
	"crypto/ecdsa"
	"fmt"
	"os"
	"path/filepath"

	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/ethclient"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	endPoint                = "http://localhost:8501"
	keyStoreFilePath        = "./examples/cpchain/data/dd1/keystore/"
	DefaultCPUDifficulty    = uint64(25)
	DefaultMemoryDifficulty = uint64(25)
)

func Connect() (*ethclient.Client, error, *ecdsa.PrivateKey, *ecdsa.PublicKey, common.Address) {
	// Create client.
	client, err := ethclient.Dial(endPoint)
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

	// Get contractAddress.
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	fmt.Println("from contractAddress:", fromAddress.Hex()) // 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a

	return client, err, privateKey, publicKeyECDSA, fromAddress
}
