package utils

import (
	"crypto/ecdsa"
	"os"
	"path/filepath"
	"strconv"

	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/cmd/cpchain/commons"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/urfave/cli"
)

// GetFirstIntArgument returns the value of the first uint64 argument
func GetFirstIntArgument(ctx *cli.Context) int64 {
	if len(ctx.Args()) != 1 {
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
	if len(ctx.Args()) != 1 {
		log.Fatal("Invalid length of arguments", "want", 1, "got", len(ctx.Args()))
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
	if len(ctx.Args()) != 1 {
		log.Fatal("Invalid length of arguments", "want", 1, "got", len(ctx.Args()))
	}

	arg := ctx.Args().Get(0)
	return arg
}

func GetFirstTwoIntArgument(ctx *cli.Context) (int64, int64) {
	if len(ctx.Args()) != 2 {
		log.Fatal("Invalid length of arguments", "want", 2, "got", len(ctx.Args()))
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

func PrepareCpclient(endpoint string) *cpclient.Client {
	client, err := cpclient.Dial(endpoint)
	if err != nil {
		log.Fatal("Failed to dial given endpoint", "endpoint", endpoint, "err", err)
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

	return client
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

func PrepareAll(ctx *cli.Context, withTransactor bool) (addr common.Address, client *cpclient.Client, key *keystore.Key) {

	endpoint := flags.GetEndpoint(ctx)
	addr = flags.GetContractAddress(ctx)
	client = PrepareCpclient(endpoint)

	if withTransactor {
		keystoreFile := flags.GetKeystorePath(ctx)
		password := GetPassword()
		_, key = GetAddressAndKey(keystoreFile, password)
	}

	return addr, client, key
}
