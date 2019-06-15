package main

import (
	"context"
	"fmt"
	"math/big"
	"os"
	"strconv"

	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/cmd/cpchain/commons"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/tools/transfer/config"
	"github.com/ethereum/go-ethereum/common"
)

//  usage:
// ./transfer http://localhost:8501 /tmp/111 0x0001 555

func main() {
	log.Info("cmdline args", "args", os.Args)
	if len(os.Args) != 5 {
		fmt.Println("Usage: transfer <endpoint> <keystore path> <to> <value>")
		return
	}

	endpoint := os.Args[1]
	keystorePath := os.Args[2]
	to := common.HexToAddress(os.Args[3])
	value, err := strconv.ParseInt(os.Args[4], 10, 64)
	log.Info("args", "endpoint", endpoint, "keystorePath", keystorePath,
		"to", to.Hex(), "value", value)
	config.SetConfig(endpoint, keystorePath)

	// ask for password
	prompt := "Unlocking account"
	password, _ := commons.ReadPassword(prompt, false)
	log.Info("password", "password", password)

	// decrypt keystore
	client, err, privateKey, _, fromAddress, kst, account := config.Connect(password)
	_, _, _ = kst, account, fromAddress

	// build parameter
	auth := bind.NewKeyedTransactor(privateKey)
	auth.From = fromAddress
	auth.Value = big.NewInt(0).SetInt64(value)

	// sendRawTransaction
	nbc := bind.NewBoundContract(to, abi.ABI{}, client, client, nil)
	tx, err := nbc.Transfer(auth)
	log.Info("sendTx", "tx", tx.Hash().Hex())

	// confirm receipt
	ctx := context.Background()
	receipt, err := bind.WaitMined(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to send transaction:%v", err)
	}
	log.Info("receipt", "status", receipt.Status)
}
