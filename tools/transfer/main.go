package main

import (
	"context"
	"fmt"
	"math/big"
	"os"
	"strconv"

	"bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/cmd/cpchain/commons"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/tools/transfer/config"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

//  usage:
// ./transfer http://192.168.0.147:8501 /tmp/src/bitbucket.org/cpchain/chain/examples/cpchain/conf-dev/keys/key1 0xc05302acebd0730e3a18a058d7d1cb1204c4a092 1
func main() {
	log.Info("cmdline args", "args", os.Args)
	if len(os.Args) != 5 {
		fmt.Println("Usage: transfer <endpoint> <keystore path> <to> <valueInWei>")
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
	prompt := "Input password to unlocking account"
	password, _ := commons.ReadPassword(prompt, false)

	// decrypt keystore
	client, err, privateKey, _, fromAddress, _, _, chainId := config.Connect(password)

	log.Infof("transfer: %v wei from: %x to: %x", value, fromAddress, to)

	printBalance(client, fromAddress, to)

	nonce, err := client.PendingNonceAt(context.Background(), fromAddress)
	if err != nil {
		log.Errorf("failed to retrieve account nonce: %v", err)
	}
	log.Infof("nonce: %v,chainId: %v", nonce, chainId)
	// Figure out the gas allowance and gas price values
	gasPrice, err := client.SuggestGasPrice(context.Background())
	if err != nil {
		log.Errorf("failed to suggest gas price: %v", err)
	}

	log.Infof("gasPrice: %v", gasPrice)
	valueInWei := big.NewInt(value)
	msg := cpchain.CallMsg{From: fromAddress, To: &to, Value: valueInWei, Data: nil}
	gasLimit, err := client.EstimateGas(context.Background(), msg)

	log.Infof("gasLimit: %v", gasLimit)
	tx := types.NewTransaction(nonce, to, valueInWei, gasLimit, gasPrice, nil)
	signedTx, err := types.SignTx(tx, types.NewCep1Signer(chainId), privateKey)
	log.Infof("signedTx: %v", signedTx.Hash().Hex())

	err = client.SendTransaction(context.Background(), signedTx)
	if err != nil {
		log.Fatalf("failed to send transaction:%v", err)
	}

	// confirm receipt
	receipt, err := bind.WaitMined(context.Background(), client, signedTx)
	if err != nil {
		log.Fatalf("failed to waitMined tx:%v", err)
	}
	if receipt.Status == types.ReceiptStatusSuccessful {

		printBalance(client, fromAddress, to)

		log.Info("confirm transaction success")
	} else {
		log.Error("confirm transaction failed", "status", receipt.Status,
			"receipt.TxHash", receipt.TxHash)
	}
}

func printBalance(client *cpclient.Client, fromAddress, to common.Address) {
	fromValue, err := client.BalanceAt(context.Background(), fromAddress, nil)
	if err != nil {
		log.Info("get from balance failed", "address", fromAddress.Hex())
	}
	log.Infof("balance: %v wei in from: %x", fromValue, fromAddress)

	toValue, err := client.BalanceAt(context.Background(), to, nil)
	if err != nil {
		log.Info("get to balance failed", "address", to.Hex())
	}
	log.Infof("balance: %v wei in to: %x", toValue, to)
}
