package main

import (
	"context"
	"math/big"
	"os"
	"strings"

	"bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/cmd/cpchain/commons"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/tools/transfer/config"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/urfave/cli"
)

func main() {

	app := cli.NewApp()
	app.Name = "transfer"
	app.Version = configs.Version
	app.Copyright = "LGPL"
	app.Usage = "Executable for CPC transfer.\n\t\tExample:./transfer --ep http://192.168.0.147:8501 --ks /tmp/keystore/key21 -t 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"

	app.Flags = []cli.Flag{
		cli.StringFlag{
			Name:  "endpoint, ep",
			Usage: "Endpoint to interact with",
			Value: "http://localhost:8501",
		},
		cli.StringFlag{
			Name:  "keystore, ks",
			Usage: "Keystore file path for from address",
			Value: "/tmp/keystore/key1",
		},

		cli.StringFlag{
			Name:  "to",
			Usage: "Recipient address",
		},

		cli.IntFlag{
			Name:  "value",
			Usage: "Value in cpc",
		},
	}
	app.Action = func(c *cli.Context) error {
		value := c.Int64("value")
		endpoint := c.String("endpoint")
		keystorePath := c.String("keystore")
		targetAddr := c.String("to")

		if !c.IsSet("value") ||
			!c.IsSet("endpoint") ||
			!c.IsSet("to") ||
			!c.IsSet("keystore") {

			return cli.NewExitError("Need more parameter ! Check parameters with ./transfer -h please. ", 1)
		}

		if isInvalidAddress(targetAddr) {
			return cli.NewExitError("invalid targetAddr:"+targetAddr, 1)
		}
		to := common.HexToAddress(targetAddr)
		log.Info("args", "endpoint", endpoint, "keystorePath", keystorePath,
			"to", to.Hex(), "value(cpc)", value)
		config.SetConfig(endpoint, keystorePath)

		// ask for password
		prompt := "Input password to unlocking account"
		password, _ := commons.ReadPassword(prompt, false)

		// decrypt keystore
		client, err, privateKey, _, fromAddress, _, _, chainId := config.Connect(password)

		log.Infof("transfer: %v cpc from: %x to: %x", value, fromAddress, to)

		printBalance(client, fromAddress, to)
		log.Info("Are you sure to continue? [Y] Yes,[N] No:")
		// confirm again
		confirm, _ := commons.ReadMessage()
		if confirm == "Y" {
			log.Info("Transfer money confirmed.")
		} else {
			log.Info("Transfer money cancelled.")
			return nil
		}

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
		valueInCpc := new(big.Int).Mul(big.NewInt(value), big.NewInt(configs.Cpc))

		msg := cpchain.CallMsg{From: fromAddress, To: &to, Value: valueInCpc, Data: nil}
		gasLimit, err := client.EstimateGas(context.Background(), msg)

		log.Infof("gasLimit: %v", gasLimit)
		tx := types.NewTransaction(nonce, to, valueInCpc, gasLimit, gasPrice, nil)
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
		return nil
	}

	err := app.Run(os.Args)
	if err != nil {
		log.Fatal("run application failed", "err", err)
	}
}
func isInvalidAddress(s string) bool {
	if strings.HasPrefix(s, "0x") {
		return len(s) != 42
	}
	return len(s) != 40
}

func printBalance(client *cpclient.Client, fromAddress, to common.Address) {
	fromValue, err := client.BalanceAt(context.Background(), fromAddress, nil)
	if err != nil {
		log.Info("get from balance failed", "address", fromAddress.Hex())
	}
	log.Infof("balance: %s wei in from address: %x", formatNumber(fromValue), fromAddress)

	toValue, err := client.BalanceAt(context.Background(), to, nil)
	if err != nil {
		log.Info("get to balance failed", "address", to.Hex())
	}
	log.Infof("balance: %s wei in to address: %x", formatNumber(toValue), to)
}

func formatNumber(value *big.Int) string {
	return value.String()

	// result := []string{}
	// valueString := value.String()
	// times := len(valueString) / 3
	// mode := len(valueString) % 3
	// if mode > 0 {
	// 	times = times + 1
	// }
	//
	// array := []rune(value.String())
	// length := len(array)
	// for i := 0; i < length; {
	// 	substr := ""
	// 	if i == 0 {
	// 		substr = string(array[0:mode])
	// 	} else {
	// 		substr = string(array[i : i+1])
	// 	}
	// 	log.Info(substr)
	//
	// 	result = append(result, substr)
	// 	i = i + 1
	// }
	// return strings.Join(result, ",")
}
