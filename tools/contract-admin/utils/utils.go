package utils

import (
	"context"
	"crypto/ecdsa"
	"errors"
	"math/big"
	"os"
	"path/filepath"
	"strconv"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/cmd/cpchain/commons"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/urfave/cli"
)

// GetFirstIntArgument returns the value of the first uint64 argument
func GetFirstIntArgument(ctx *cli.Context) int64 {
	if ctx.NArg() != 1 {
		log.Fatal("Invalid length of arguments", "want", 1, "got", len(ctx.Args()))
	}

	arg := ctx.Args().Get(0)
	v, err := strconv.Atoi(arg)
	if err != nil {
		log.Fatal("Failed to parse value", "value", arg, "err", err)
	}

	return int64(v)
}

func GetFirstBoolArgument(ctx *cli.Context) bool {
	if ctx.NArg() != 1 {
		log.Fatal("Invalid length of arguments", "want", 1, "got", ctx.NArg())
	}

	arg := ctx.Args().Get(0)
	if arg == "true" || arg == "True" || arg == "TRUE" {
		return true
	} else if arg == "false" || arg == "False" || arg == "FALSE" {
		return false
	} else {
		log.Fatal("Invalid argument", "want", "bool", "got", arg)
	}

	return false
}

// GetFirstStringArgument returns the value of the first string argument
func GetFirstStringArgument(ctx *cli.Context) string {
	if ctx.NArg() != 1 {
		log.Fatal("Invalid length of arguments", "want", 1, "got", ctx.NArg())
	}

	arg := ctx.Args().Get(0)
	return arg
}

func GetFirstTwoIntArgument(ctx *cli.Context) (int64, int64) {
	if ctx.NArg() != 2 {
		log.Fatal("Invalid length of arguments", "want", 2, "got", ctx.NArg())
	}

	arg1 := ctx.Args().Get(0)
	v1, err := strconv.Atoi(arg1)
	if err != nil {
		log.Fatal("Failed to parse value", "value", arg1, "err", err)
	}

	arg2 := ctx.Args().Get(1)
	v2, err := strconv.Atoi(arg2)
	if err != nil {
		log.Fatal("Failed to parse value", "value", arg2, "err", err)
	}

	return int64(v1), int64(v2)
}

func GetAddressAndKey(keystoreFilePath, password string) (common.Address, *keystore.Key) {

	// Open keystore file.
	file, err := os.Open(keystoreFilePath)
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
	account, key, err := kst.GetDecryptedKey(account, password)
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

	return fromAddress, key
}

func PrepareCpclient(endpoint string) (*cpclient.Client, error) {
	client, err := cpclient.Dial(endpoint)
	if err != nil {
		log.Info("Failed to dial given endpoint", "endpoint", endpoint, "err", err)
		return &cpclient.Client{}, errors.New("Failed to dial given endpoint")
	}

	chainConfig, err := client.ChainConfig()
	if err != nil {
		log.Info(err.Error())
		return &cpclient.Client{}, err
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
		log.Info("unknown chain id")
		return &cpclient.Client{}, errors.New("unknown chain id")
	}
	configs.SetRunMode(runMode)

	return client, nil
}

func GetPassword() string {
	// get password and unlock keystore file, then update `key`
	prompt := "Input password to unlocking account"
	password, err := commons.ReadPassword(prompt, false)
	if err != nil {
		log.Fatal("Failed to read password", "err", err)
	}

	return password
}

func PrepareAll(ctx *cli.Context, withTransactor bool) (addr common.Address, client *cpclient.Client, key *keystore.Key, err error) {

	endpoint, err := flags.GetEndpoint(ctx)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	addr, err = flags.GetContractAddress(ctx)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	client, err = PrepareCpclient(endpoint)
	if err != nil {
		return common.Address{}, nil, nil, err
	}

	if withTransactor {
		keystoreFile, err := flags.GetKeystorePath(ctx)
		if err != nil {
			return common.Address{}, &cpclient.Client{}, &keystore.Key{}, err
		}
		password := GetPassword()
		_, key = GetAddressAndKey(keystoreFile, password)
	}

	return addr, client, key, nil
}

func WaitMined(client *cpclient.Client, tx *types.Transaction) error {

	log.Info("Transaction sent", "hash", tx.Hash().Hex())

	receipt, err := bind.WaitMined(context.Background(), client, tx)
	if err != nil {
		log.Info("Failed to wait for tx being mined", "tx", tx.Hash().Hex(), "err", err)
		return cli.NewExitError(err, 1)
	}

	log.Info("Transaction has been mined", "hash", receipt.TxHash.Hex(), "status", receipt.Status)
	if receipt.Status != types.ReceiptStatusSuccessful {
		return cli.NewExitError("receipt status is "+string(receipt.Status), 1)
	}
	return nil
}

// PrintBalance print balance of the address
func PrintBalance(client *cpclient.Client, fromAddress common.Address) {
	fromValue, err := client.BalanceAt(context.Background(), fromAddress, nil)
	if err != nil {
		log.Info("get from balance failed", "address", fromAddress.Hex())
	}
	log.Infof("balance: %v [wei],\tabout %v [cpc] in address: %x", fromValue, new(big.Int).Div(fromValue, big.NewInt(configs.Cpc)), fromAddress)
}
