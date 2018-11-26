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

package config

import (
	"crypto/ecdsa"
	"os"
	"path/filepath"

	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	endPoint                = "http://localhost:8501"
	// @xumx cleanup.  why absolute path?
	keyStoreFilePath        = "/chain/examples/cpchain/data/data1/keystore/"
	DefaultCPUDifficulty    = uint64(25)
	DefaultMemoryDifficulty = uint64(25)
)

// overwrite from environment variables
func init() {
	if val := os.Getenv("CPCHAIN_KEYSTORE_FILEPATH"); val != "" {
		keyStoreFilePath = val
	}
}

func Connect() (*cpclient.Client, error, *ecdsa.PrivateKey, *ecdsa.PublicKey, common.Address) {
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

	// Get contractAddress.
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	// fmt.Println("from contractAddress:", fromAddress.Hex()) // 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a

	return client, err, privateKey, publicKeyECDSA, fromAddress
}
