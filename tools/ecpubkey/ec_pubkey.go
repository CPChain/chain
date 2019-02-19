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

// export ec public key from keyfile
func main() {
	if len(os.Args) < 3 {
		fmt.Println("Error! Need 2 parameters:./ecpubkey <keyFile> <password>\nexample:./ecpubkey examples/cpchain/conf-dev/keys/key1 password")
		return
	}

	var keyFile = ""
	var password = "password"
	args := os.Args
	if len(args) > 1 {
		fmt.Println("keyFile:", args[1])
		keyFile = args[1]
	}
	if len(args) > 2 {
		fmt.Println("password:", args[2])
		password = args[2]
	}

	pubKey, err := ecdsaPubKey(keyFile, password)
	if err != nil {
		fmt.Println("error:", err)
	}
	fmt.Println("\npubKey is:\n" + pubKey)
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
