// Copyright 2018 The cpchain authors

package main

import (
	"fmt"
	"io/ioutil"
	"os"

	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/commons/crypto/ecieskey"
	"github.com/ethereum/go-ethereum/common/hexutil"
)

func main() {
	var keyFile = ""
	var password = "password"
	args := os.Args
	fmt.Println("0", args[0])
	if len(args) > 1 {
		fmt.Println("1", args[1])
		keyFile = args[1]
	}
	if len(args) > 2 {
		fmt.Println("2", args[2])
		password = args[2]
	}

	if keyFile == "" {
		keyFile = "examples/cpchain/conf-dev/keys/key1"
	}

	if password == "" {
		password = "password"
	}

	pubKey, err := ecdsaPubKey(keyFile, password)
	if err != nil {
		fmt.Println("error:", err)
	}
	fmt.Println("pubKey:", pubKey)
}

func ecdsaPubKey(keyfilePath, password string) (string, error) {
	keyjson, _ := ioutil.ReadFile(keyfilePath)

	key, err := keystore.DecryptKey(keyjson, password)
	if err != nil {
		return "", err
	}
	bytes := ecieskey.EncodeEcdsaPubKey(&key.PrivateKey.PublicKey)
	return hexutil.Encode(bytes), nil
}
