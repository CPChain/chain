package main

import (
	"context"
	"fmt"
	"math/big"
	"os"
	"strconv"

	"bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/cmd/cpchain/commons"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/tools/transfer/config"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

//  usage:
// ./transfer [mainnet|dev|testmainnet] http://192.168.0.147:8501 /home/xmx0632/workspace/chain_new/src/bitbucket.org/cpchain/chain/examples/cpchain/conf-dev/keys/key1 0xc05302acebd0730e3a18a058d7d1cb1204c4a092 1
// ./transfer mainnet http://192.168.0.147:8501 /home/xmx0632/workspace/chain_new/src/bitbucket.org/cpchain/chain/examples/cpchain/conf-dev/keys/key1 0xc05302acebd0730e3a18a058d7d1cb1204c4a092 1
func main() {
	log.Info("cmdline args", "args", os.Args)
	if len(os.Args) != 6 {
		fmt.Println("Usage: transfer <type> <endpoint> <keystore path> <to> <value>")
		return
	}

	chainType := os.Args[1]

	chainId := getChainId(chainType)

	endpoint := os.Args[2]
	keystorePath := os.Args[3]
	to := common.HexToAddress(os.Args[4])
	value, err := strconv.ParseInt(os.Args[5], 10, 64)
	log.Info("args", "endpoint", endpoint, "keystorePath", keystorePath,
		"to", to.Hex(), "value", value)
	config.SetConfig(endpoint, keystorePath)

	// ask for password
	prompt := "Input password to unlocking account"
	password, _ := commons.ReadPassword(prompt, false)

	// decrypt keystore
	client, err, privateKey, _, fromAddress, kst, account := config.Connect(password)
	_, _, _ = kst, account, fromAddress

	nonce, err := client.PendingNonceAt(context.Background(), fromAddress)
	if err != nil {
		log.Errorf("failed to retrieve account nonce: %v", err)
	}
	log.Infof("nonce: %v", nonce)
	// Figure out the gas allowance and gas price values
	gasPrice, err := client.SuggestGasPrice(context.Background())
	if err != nil {
		log.Errorf("failed to suggest gas price: %v", err)
	}

	log.Infof("gasPrice: %v", gasPrice)
	vv := big.NewInt(value)
	msg := cpchain.CallMsg{From: fromAddress, To: &to, Value: vv, Data: nil}
	gasLimit, err := client.EstimateGas(context.Background(), msg)

	log.Infof("gasLimit: %v", gasLimit)
	tx := types.NewTransaction(nonce, to, vv, gasLimit, gasPrice, nil)
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
		log.Info("confirm transaction success")
	} else {
		log.Error("confirm transaction failed", "status", receipt.Status,
			"receipt.TxHash", receipt.TxHash)
	}
}
func getChainId(chainType string) *big.Int {
	switch chainType {
	case "mainnet":
		return big.NewInt(configs.MainnetChainId)
	case "testmainnet":
		return big.NewInt(configs.TestMainnetChainId)
	case "dev":
		return big.NewInt(configs.DevChainId)
	default:
		return big.NewInt(configs.MainnetChainId)
	}
}
