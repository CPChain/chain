// Copyright 2018 The cpchain authors

package main

import (
	"encoding/hex"
	"fmt"
	"io/ioutil"
	"os"
	"strings"

	"bitbucket.org/cpchain/chain/accounts/keystore"
)

func main() {
	dir, err := ioutil.TempDir("", "convert-key-test")
	if err != nil {
		fmt.Println("err", err)
	}
	// defer os.RemoveAll(dir)

	var keyDir = ""
	args := os.Args
	fmt.Println("0", args[0])
	if len(args) > 1 {
		fmt.Println("1", args[1])
		keyDir = args[1]
	}
	if len(args) > 2 {
		fmt.Println("2", args[2])
	}

	if keyDir == "" {
		keyDir = "examples/cpchain/conf-dev/keys"
	}
	if keys, err := ioutil.ReadDir(keyDir); err == nil {
		for _, key := range keys {
			fmt.Println("file:", key.Name())
			keyjson, _ := ioutil.ReadFile(keyDir + "/" + key.Name())
			password := "password"
			switch key.Name() {
			case "key3":
				password = "pwdnode1"
			case "key4":
				password = "pwdnode2"
			default:
				password = "password"
			}
			mac, newMac := keystore.ExtractDiffMac(keyjson, password)
			fmt.Printf("mac:%x, newMac:%x\n", mac, newMac)
			keyString := string(keyjson)
			newJson := strings.Replace(keyString, hex.EncodeToString(mac), hex.EncodeToString(newMac), 1)
			newPath := dir + "/" + key.Name()
			fmt.Println("newPath:", newPath)
			fmt.Println("newJson:", newJson)
			ioutil.WriteFile(newPath, []byte(newJson), 0644)
		}
	}
}
