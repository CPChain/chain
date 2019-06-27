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

	"math/big"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/pkg/errors"
)

var (
	endPoint         = "http://localhost:8501"
	keyStoreFilePath = "./chain/examples/cpchain/data/data1/keystore/"
)

// overwrite from environment variables
func init() {
	if val := os.Getenv("CPCHAIN_KEYSTORE_FILEPATH"); val != "" {
		keyStoreFilePath = val
	}
}

func SetConfig(ep, ksPath string) {
	endPoint = ep
	keyStoreFilePath = ksPath
}

func Connect(password string) (*cpclient.Client, error, *ecdsa.PrivateKey, *ecdsa.PublicKey, common.Address, *keystore.KeyStore, accounts.Account, *big.Int) {
	ep, err := configs.ResolveUrl(endPoint)
	if err != nil {
		log.Fatal("unknown endpoint", "endpoint", endPoint, "err", err)
	}
	// Create client.
	client, err := cpclient.Dial(ep)
	if err != nil {
		log.Fatal(err.Error())
	}

	chainConfig, err := client.ChainConfig()
	if err != nil {
		log.Fatal(err.Error())
	}
	chainId, runMode := chainConfig.ChainID.Uint64(), configs.Mainnet
	switch chainId {
	case configs.DevChainId:
		runMode = configs.Dev
	case configs.MainnetChainId:
		runMode = configs.Mainnet
	case configs.TestMainnetChainId:
		runMode = configs.TestMainnet
	case configs.TestnetChainId:
		runMode = configs.Testnet
	default:
		log.Fatal("unknown chain id")
	}
	configs.SetRunMode(runMode)

	privateKey, publicKeyECDSA, fromAddress, kst, account, err := DecryptKeystore(password)
	if err != nil {
		log.Fatal(err.Error())
	}
	return client, err, privateKey, publicKeyECDSA, fromAddress, kst, account, big.NewInt(0).SetUint64(chainId)
}

func DecryptKeystore(password string) (*ecdsa.PrivateKey, *ecdsa.PublicKey, common.Address, *keystore.KeyStore, accounts.Account, error) {
	// Open keystore file.
	file, err := os.Open(keyStoreFilePath)
	if err != nil {
		return nil, nil, [20]byte{}, nil, accounts.Account{}, err
	}
	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	if err != nil {
		return nil, nil, [20]byte{}, nil, accounts.Account{}, err
	}
	// Create keystore and get account.
	kst := keystore.NewKeyStore(keyPath, 2, 1)
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, password)
	if err != nil {
		return nil, nil, [20]byte{}, nil, accounts.Account{}, err
	}
	// Get private and public keys.
	privateKey := key.PrivateKey
	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		return nil, nil, [20]byte{}, nil, accounts.Account{}, errors.New("error casting public key to ECDSA")
	}

	// Get contractAddress.
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	return privateKey, publicKeyECDSA, fromAddress, kst, account, nil

}
