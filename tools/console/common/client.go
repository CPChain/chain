package common

import (
	"crypto/ecdsa"
	"os"
	"path/filepath"

	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

// NewCpcClient new a cpc.client
func NewCpcClient(ep string, kspath string, password string) (*cpclient.Client, *ecdsa.PrivateKey, *ecdsa.PublicKey, common.Address, error) {
	// Create client.
	client, err := cpclient.Dial(ep)
	if err != nil {
		return nil, nil, nil, [20]byte{}, err
	}
	// Open keystore file.
	file, err := os.Open(kspath)
	if err != nil {
		return nil, nil, nil, [20]byte{}, err
	}
	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	if err != nil {
		return nil, nil, nil, [20]byte{}, err
	}
	// Create keystore and get account.
	kst := keystore.NewKeyStore(keyPath, 2, 1)
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, password)
	if err != nil {
		return nil, nil, nil, [20]byte{}, err
	}
	// Get private and public keys.
	privateKey := key.PrivateKey
	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		return nil, nil, nil, [20]byte{}, err
	}

	// Get contractAddress.
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	// fmt.Println("from contractAddress:", fromAddress.Hex()) // 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a

	return client, privateKey, publicKeyECDSA, fromAddress, err
}
