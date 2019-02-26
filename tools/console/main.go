package main

import (
	"fmt"
	"os"

	"bitbucket.org/cpchain/chain/tools/console/common"
	Output "bitbucket.org/cpchain/chain/tools/console/output"
)

var (
	endPoint         = "http://localhost:8501"
	keyStoreFilePath = "~/.cpchain/keystore/"
)

func init() {
	if val := os.Getenv("CPCHAIN_KEYSTORE_FILEPATH"); val != "" {
		keyStoreFilePath = val
	}
}

func main() {
	endPoint = "http://3.0.61.106:8523"
	keyStoreFilePath = "/Users/liaojinlong/.cpchain/keystore/"
	password := "password"
	output := Output.NewLogOutput()
	client, privateKey, publicKeyECDSA, fromAddress, err := common.NewCpcClient(endPoint, keyStoreFilePath, password)
	if err != nil {
		output.Fatal(err.Error())
	}
	fmt.Println(client)
	fmt.Println(privateKey)
	fmt.Println(publicKeyECDSA)
	fmt.Println(fromAddress)
	fmt.Println("Hello world")
}
