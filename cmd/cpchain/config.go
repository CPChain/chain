package main

import (
	"crypto/ecdsa"
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/crypto"
	"bitbucket.org/cpchain/chain/network/protocols/cpc"
	"bitbucket.org/cpchain/chain/node"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
	"github.com/naoina/toml"
	"github.com/urfave/cli"
)

type config struct {
	Eth  cpc.Config
	Node node.Config
}

func updateDataDirFlag(ctx *cli.Context, cfg *node.Config) {
	if ctx.IsSet(flags.DataDirFlagName) {
		cfg.DataDir = ctx.String(flags.DataDirFlagName)
	}
}

func updateNodeGeneralConfig(ctx *cli.Context, cfg *node.Config) {
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
	updateBootstrapNodes(ctx, cfg)
	updateNodeKey(ctx, cfg)
}

// updateBootstrapNodes creates a list of bootstrap nodes from the command line
// flags, reverting to pre-configured ones if none have been specified.
func updateBootstrapNodes(ctx *cli.Context, cfg *p2p.Config) {
	urls := configs.CpchainBootnodes // TODO: CPChain boot nodes should be mainnet
	if ctx.IsSet(flags.BootnodesFlagName) {
		urls = strings.Split(ctx.String(flags.BootnodesFlagName), ",")
	}

	// TODO should we switch to disv5? @jason
	cfg.BootstrapNodes = make([]*discover.Node, 0, len(urls))
	for _, url := range urls {
		node, err := discover.ParseNode(url)
		if err != nil {
			log.Error("Bootstrap URL invalid", "enode", url, "err", err)
			continue
		}
		cfg.BootstrapNodes = append(cfg.BootstrapNodes, node)
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

// TODO @sangh
func updateRpcConfig(ctx *cli.Context, cfg *node.Config) {
}

func updateNodeConfig(ctx *cli.Context, cfg *node.Config) {
	updateNodeGeneralConfig(ctx, cfg)
	updateP2pConfig(ctx, &cfg.P2P)
	updateRpcConfig(ctx, cfg)

	if ctx.IsSet(flags.LightKdfFlagName) {
		cfg.UseLightweightKDF = ctx.Bool(flags.LightKdfFlagName)
	}
}

// begin chain configs ********************************************************************88

// Updates the account for cfg.Etherbase
func updateBaseAccount(ctx *cli.Context, ks *keystore.KeyStore, cfg *cpc.Config) {
	if ctx.IsSet("account") {
		val := ctx.String("account")
		if !common.IsHexAddress(val) {
			log.Fatalf("Invalid account hex address: %v", val)
		}
		account := accounts.Account{Address: common.HexToAddress(val)}
		cfg.Etherbase = account.Address
	} else {
		isRunCommand := ctx.Command.Name == runCommand.Name
		// fall back on the first account
		accs := ks.Accounts()
		if len(accs) > 0 {
			account := accs[0].Address
			cfg.Etherbase = account
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

}

func updateChainGeneralConfig(ctx *cli.Context, cfg *cpc.Config) {
	// network id setup
	if ctx.IsSet("networkid") {
		cfg.NetworkId = ctx.Uint64("networkid")
	}
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
		Eth:  cpc.DefaultConfig,
		Node: node.DefaultConfig,
	}
	// update data dir first
	updateDataDirFlag(ctx, &cfg.Node)

	updateConfigFromFile(ctx, &cfg)

	// now update from command line arguments
	updateNodeConfig(ctx, &cfg.Node)

	// create node
	n, err := node.New(&cfg.Node)
	if err != nil {
		log.Fatalf("Node creation failed: %v", err)
	}

	// update chain config
	updateChainConfig(ctx, &cfg.Eth, n)

	return cfg, n
}
