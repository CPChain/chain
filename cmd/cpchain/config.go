// Copyright 2016 The go-ethereum Authors
// Copyright 2018 The cpchain authors
// This file is part of cpchain.
//
// cpchain is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// cpchain is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with cpchain. If not, see <http://www.gnu.org/licenses/>.

package main

import (
	"crypto/ecdsa"
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"strings"

	"bitbucket.org/cpchain/chain/protocols/cpc/syncer"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/node"
	"bitbucket.org/cpchain/chain/protocols/cpc"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
	"github.com/naoina/toml"
	"github.com/urfave/cli"
)

var (
	isRunningChain = false
)

type config struct {
	Cpc  cpc.Config
	Node node.Config
}

func updateRunModeFlag(ctx *cli.Context) {
	if ctx.IsSet(flags.RunModeFlagName) {
		runMode := configs.RunMode(ctx.String(flags.RunModeFlagName))
		configs.SetRunMode(runMode)
	}
}

func updateDataDirFlag(ctx *cli.Context, cfg *node.Config) {
	if ctx.IsSet(flags.DataDirFlagName) {
		cfg.DataDir = ctx.String(flags.DataDirFlagName)
	}
}

func updateLogConfig(ctx *cli.Context) {
	if ctx.IsSet(flags.VerbosityFlagName) {
		verbosity := ctx.Uint(flags.VerbosityFlagName)
		if verbosity > 5 {
			log.Error("log level error, use default info level")
		}
		log.SetLevel(log.Level(verbosity))
	}

	if ctx.IsSet(flags.LineNumberFlagName) {
		if ctx.Bool(flags.LineNumberFlagName) {
			log.ShowFilename()
		}
	}

	if ctx.IsSet(flags.LogFileFlagName) {
		filename := ctx.String(flags.LogFileFlagName)
		f, err := os.OpenFile(filename, os.O_WRONLY|os.O_CREATE|os.O_APPEND, 0644)
		if err != nil {
			log.Error("Error: create output file of logger")
		} else {
			log.SetOutput(f)
		}
	}
}

func updateNodeGeneralConfig(ctx *cli.Context, cfg *node.Config) {
	updateRunModeFlag(ctx)

	// log update
	updateLogConfig(ctx)

	// identity
	if ctx.IsSet(flags.IdentityFlagName) {
		cfg.UserIdent = ctx.String(flags.IdentityFlagName)
	}
}

func updateP2pConfig(ctx *cli.Context, cfg *p2p.Config) {
	// max peers
	if ctx.IsSet(flags.MaxPeersFlagName) {
		cfg.MaxPeers = ctx.Int(flags.MaxPeersFlagName)
	}
	// max pending peers
	if ctx.IsSet(flags.MaxPendingPeersFlagName) {
		cfg.MaxPendingPeers = ctx.Int(flags.MaxPendingPeersFlagName)
	}
	// port
	if ctx.IsSet(flags.PortFlagName) {
		cfg.ListenAddr = fmt.Sprintf(":%d", ctx.Int(flags.PortFlagName))
	}

	if isRunningChain {
		updateBootstrapNodes(ctx, cfg)
		updateValidatorNodes(ctx)
		updateGenesisAddress(ctx)
	}
	updateNodeKey(ctx, cfg)
}

// updateBootstrapNodes creates a list of bootstrap nodes from the command line
// flags, reverting to pre-configured ones if none have been specified.
func updateBootstrapNodes(ctx *cli.Context, cfg *p2p.Config) {
	urls := configs.Bootnodes()
	if ctx.IsSet(flags.BootnodesFlagName) {
		urls = strings.Split(ctx.String(flags.BootnodesFlagName), ",")
	}

	cfg.BootstrapNodes = make([]*discover.Node, 0, len(urls))
	newUrls, err := configs.ConvertNodeURL(urls)
	log.Debug("convert bootnode urls", "original urls", urls, "new urls", newUrls)
	if err != nil {
		log.Fatal("convertValidators failed", "error", err)
	}

	for _, url := range newUrls {
		node, err := discover.ParseNode(url)
		if err != nil {
			log.Error("Bootstrap URL invalid", "enode", url, "err", err)
			continue
		}
		cfg.BootstrapNodes = append(cfg.BootstrapNodes, node)
	}
}

// updateValidatorNodes creates a list of validator nodes from the command line
// flags, reverting to pre-configured ones if none have been specified.
func updateValidatorNodes(ctx *cli.Context) {
	var urls []string
	if ctx.IsSet(flags.ValidatorsFlagName) {
		urls = strings.Split(ctx.String(flags.ValidatorsFlagName), ",")
	}
	configs.InitDefaultValidators(urls)
}

// updateGenesisAddress set the default candidates/validators/proposers
func updateGenesisAddress(ctx *cli.Context) {
	if ctx.IsSet(flags.GenesisFlagName) {
		genesisPath := ctx.String(flags.GenesisFlagName)
		file, err := os.Open(genesisPath)
		if err != nil {
			log.Fatalf("Failed to read genesis file: %v", err)
		}
		defer file.Close()

		genesis := new(core.Genesis)
		if err := toml.NewDecoder(file).Decode(genesis); err != nil {
			log.Fatalf("invalid genesis file: %v", err)
		}
		configs.SetDefaultCandidates(genesis.Candidates)
		configs.SetDefaultProposers(genesis.Dpor.Proposers)
		configs.SetDefaultValidators(genesis.Dpor.Validators)
	}
}

// Update node key from a specified file
func updateNodeKey(ctx *cli.Context, cfg *p2p.Config) {
	var (
		file = ctx.String(flags.NodeKeyFileFlagName)
		key  *ecdsa.PrivateKey
		err  error
	)

	if file != "" {
		if key, err = crypto.LoadECDSA(file); err != nil {
			log.Fatalf("Option --%q: %v", flags.NodeKeyFileFlagName, err)
		}
		cfg.PrivateKey = key
	}
}

func updateRpcConfig(ctx *cli.Context, cfg *node.Config) {
	// ipc setting
	if ctx.IsSet(flags.IpcAddrFlagName) {
		cfg.IPCPath = ctx.String(flags.IpcAddrFlagName)
	}

	// http setting
	if ctx.IsSet(flags.RpcAddrFlagName) {
		addr := strings.Split(ctx.String(flags.RpcAddrFlagName), ":")
		if len(addr) != 2 {
			log.Fatalf("Wrong number of arguments for --%v flag\n", flags.RpcAddrFlagName)
		}
		cfg.HTTPHost = addr[0]
		cfg.HTTPPort, _ = strconv.Atoi(addr[1])
	}
	if ctx.IsSet(flags.RpcApiFlagName) {
		cfg.HTTPModules = strings.Split(ctx.String(flags.RpcApiFlagName), ",")
		log.Infof("HTTPModules:%v", cfg.HTTPModules)
	}

	// ws is omitted for now

	if ctx.IsSet(flags.RpcCorsDomainFlagName) {
		cfg.HTTPCors = strings.Split(ctx.String(flags.RpcCorsDomainFlagName), ",")
	}
}

func updateNodeConfig(ctx *cli.Context, cfg *node.Config) {
	updateNodeGeneralConfig(ctx, cfg)
	updateP2pConfig(ctx, &cfg.P2P)
	updateRpcConfig(ctx, cfg)

	if ctx.IsSet(flags.LightKdfFlagName) {
		cfg.UseLightweightKDF = ctx.Bool(flags.LightKdfFlagName)
	}
}

// begin chain configs

// Updates the account for cfg.Coinbase
func updateBaseAccount(ctx *cli.Context, ks *keystore.KeyStore, cfg *cpc.Config) {
	if ctx.IsSet("account") {
		val := ctx.String("account")
		if !common.IsHexAddress(val) {
			log.Fatalf("Invalid account hex address: %v", val)
		}
		account := accounts.Account{Address: common.HexToAddress(val)}
		cfg.Cpcbase = account.Address
	} else {
		isRunCommand := ctx.Command.Name == runCommand.Name
		// fall back on the first account
		accs := ks.Accounts()
		if len(accs) > 0 {
			account := accs[0].Address
			cfg.Cpcbase = account
			// only log if we are running
			if isRunCommand {
				log.Warnf("Use account %v as the default account.", account.String())
			}
		} else {
			if isRunCommand {
				log.Warn("No default account to use.")
			}
		}
	}
}

// Updates transaction pool configurations
func updateTxPool(ctx *cli.Context, cfg *core.TxPoolConfig) {
	if ctx.IsSet(flags.MaxTxMapSizeFlagName) {
		cfg.MaxTxMapSize = ctx.Uint64(flags.MaxTxMapSizeFlagName)
	}
	if ctx.IsSet(flags.FifoTxPoolQueue) {
		cfg.IsFifoTxQueue = ctx.Bool(flags.FifoTxPoolQueue)

	}
}

func updateChainGeneralConfig(ctx *cli.Context, cfg *cpc.Config) {
	// network id setup
	// default
	cfg.NetworkId = configs.DevNetworkId

	runMode := configs.GetRunMode()
	log.Debug("runMode", "runMode", runMode)
	switch runMode {
	case configs.Dev:
		cfg.NetworkId = configs.DevNetworkId
	case configs.Testnet:
		cfg.NetworkId = configs.TestnetNetworkId
	case configs.Mainnet:
		cfg.NetworkId = configs.MainnetNetworkId
	case configs.TestMainnet:
		cfg.NetworkId = configs.TestMainnetNetworkId
	}

	// specific
	if ctx.IsSet(flags.NetworkIDFlagName) {
		cfg.NetworkId = ctx.Uint64(flags.NetworkIDFlagName)
	}
	log.Debug("update networkId", "networkId", cfg.NetworkId)
}

// Updates chain configuration
func updateChainConfig(ctx *cli.Context, cfg *cpc.Config, n *node.Node) {
	updateChainGeneralConfig(ctx, cfg)
	// passing in a node, all for this.  a pity.
	ks := n.AccountManager().Backends(keystore.KeyStoreType)[0].(*keystore.KeyStore)
	updateBaseAccount(ctx, ks, cfg)
	// setGPO(ctx, &cfg.GPO)
	updateTxPool(ctx, &cfg.TxPool)
	updateDatabaseCache(ctx, cfg)
	updateTrieCache(ctx, cfg)
}

// updateDatabaseCache updates database cache.
func updateDatabaseCache(ctx *cli.Context, cfg *cpc.Config) {
	if ctx.IsSet(flags.CacheFlagName) && ctx.IsSet(flags.CacheDatabaseFlagName) {
		cfg.DatabaseCache = ctx.Int(flags.CacheFlagName) * ctx.Int(flags.CacheDatabaseFlagName) / 100
	}
}

// updateTrieCache updates trie cache.
func updateTrieCache(ctx *cli.Context, cfg *cpc.Config) {
	if ctx.IsSet(flags.CacheFlagName) && ctx.IsSet(flags.CacheGCFlagName) {
		cfg.TrieCache = ctx.Int(flags.CacheFlagName) * ctx.Int(flags.CacheGCFlagName) / 100
	}
}

// updateTrieCache updates trie cache.
func updateSyncModeFlag(ctx *cli.Context, cfg *cpc.Config) {
	if ctx.IsSet(flags.FastSyncFlagName) {
		cfg.SyncMode = syncer.FastSync
	}
}

// Updates config from --config file
func updateConfigFromFile(ctx *cli.Context, cfg *config) {
	var path string
	if ctx.GlobalIsSet("config") {
		p := ctx.GlobalString("config")
		if _, err := os.Stat(p); os.IsNotExist(err) {
			log.Fatalf("Config file doesn't exist: %v", p)
		}
		path = p
	} else {
		// try to read from the datadir/config.toml
		p := filepath.Join(cfg.Node.DataDir, "config.toml")
		if _, err := os.Stat(p); !os.IsNotExist(err) {
			path = p
		}
	}

	if path != "" {
		log.Infof("Load config file from: %v", path)
		f, err := os.Open(path)
		if err != nil {
			log.Fatalf("Invalid TOML config file: %v", err)
		}
		defer f.Close()
		decoder := toml.NewDecoder(f)
		if err := decoder.Decode(cfg); err != nil {
			log.Fatalf("Invalid TOML config file: %v", err)
		}
	}
}

// Creates a config and a node
func newConfigNode(ctx *cli.Context) (config, *node.Node) {
	// default
	cfg := config{
		Cpc:  cpc.DefaultConfig,
		Node: node.DefaultConfig,
	}

	// update data dir first
	updateDataDirFlag(ctx, &cfg.Node)
	updateConfigFromFile(ctx, &cfg)

	// now update from command line arguments
	// set runmode at first
	updateRunModeFlag(ctx)
	updateNodeConfig(ctx, &cfg.Node)

	updateSyncModeFlag(ctx, &cfg.Cpc)

	// create node
	n, err := node.New(&cfg.Node)
	if err != nil {
		log.Fatalf("Node creation failed: %v", err)
	}

	// update chain config
	updateChainConfig(ctx, &cfg.Cpc, n)

	return cfg, n
}
