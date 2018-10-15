package main

import (
	"os"
	"path/filepath"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/eth"
	"bitbucket.org/cpchain/chain/node"
	"github.com/BurntSushi/toml"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/urfave/cli"
)

type config struct {
	Eth  eth.Config
	Node node.Config
}

// begin some flag specific function
// ***********************************************************
func updateDataDirFlag(ctx *cli.Context, cfg *node.Config) {
	if ctx.IsSet("datadir") {
		cfg.DataDir = ctx.String("datadir")
	}
}

func updateNodeGeneralConfig(ctx *cli.Context, cfg *node.Config) {
	updateDataDirFlag(ctx, cfg)
	// update identity
	if ctx.IsSet("identity") {
		cfg.UserIdent = ctx.String("identity")
	}
}

func updateP2pConfig(ctx *cli.Context, cfg *p2p.Config) {
}

// TODO @sangh
func updateRpcConfig(ctx *cli.Context, cfg *node.Config) {
}

func updateChainConfig(ctx *cli.Context, cfg *eth.Config, n *node.Node) {
	// ks := n.AccountManager().Backends(keystore.KeyStoreType)[0].(*keystore.KeyStore)
	// setEtherbase(ctx, ks, cfg)
	// setGPO(ctx, &cfg.GPO)
	// setTxPool(ctx, &cfg.TxPool)
	// setEthash(ctx, cfg)
	//
	// switch {
	// case ctx.GlobalIsSet(SyncModeFlag.Name):
	// 	cfg.SyncMode = *GlobalTextMarshaler(ctx, SyncModeFlag.Name).(*downloader.SyncMode)
	// case ctx.GlobalBool(FastSyncFlag.Name):
	// 	cfg.SyncMode = downloader.FastSync
	// case ctx.GlobalBool(LightModeFlag.Name):
	// 	cfg.SyncMode = downloader.LightSync
	// }
	// if ctx.GlobalIsSet(LightServFlag.Name) {
	// 	cfg.LightServ = ctx.GlobalInt(LightServFlag.Name)
	// }
	// if ctx.GlobalIsSet(LightPeersFlag.Name) {
	// 	cfg.LightPeers = ctx.GlobalInt(LightPeersFlag.Name)
	// }
	// if ctx.GlobalIsSet(NetworkIdFlag.Name) {
	// 	cfg.NetworkId = ctx.GlobalUint64(NetworkIdFlag.Name)
	// }
	//
	// if ctx.GlobalIsSet(CacheFlag.Name) || ctx.GlobalIsSet(CacheDatabaseFlag.Name) {
	// 	cfg.DatabaseCache = ctx.GlobalInt(CacheFlag.Name) * ctx.GlobalInt(CacheDatabaseFlag.Name) / 100
	// }
	// cfg.DatabaseHandles = makeDatabaseHandles()
	//
	// if gcmode := ctx.GlobalString(GCModeFlag.Name); gcmode != "full" && gcmode != "archive" {
	// 	Fatalf("--%s must be either 'full' or 'archive'", GCModeFlag.Name)
	// }
	// cfg.NoPruning = ctx.GlobalString(GCModeFlag.Name) == "archive"
	//
	// if ctx.GlobalIsSet(CacheFlag.Name) || ctx.GlobalIsSet(CacheGCFlag.Name) {
	// 	cfg.TrieCache = ctx.GlobalInt(CacheFlag.Name) * ctx.GlobalInt(CacheGCFlag.Name) / 100
	// }
	// if ctx.GlobalIsSet(MinerThreadsFlag.Name) {
	// 	cfg.MinerThreads = ctx.GlobalInt(MinerThreadsFlag.Name)
	// }
	// if ctx.GlobalIsSet(DocRootFlag.Name) {
	// 	cfg.DocRoot = ctx.GlobalString(DocRootFlag.Name)
	// }
	// if ctx.GlobalIsSet(ExtraDataFlag.Name) {
	// 	cfg.ExtraData = []byte(ctx.GlobalString(ExtraDataFlag.Name))
	// }
	// if ctx.GlobalIsSet(GasPriceFlag.Name) {
	// 	cfg.GasPrice = GlobalBig(ctx, GasPriceFlag.Name)
	// }
	// if ctx.GlobalIsSet(VMEnableDebugFlag.Name) {
	// 	// TODO(fjl): force-enable this in --dev mode
	// 	cfg.EnablePreimageRecording = ctx.GlobalBool(VMEnableDebugFlag.Name)
	// }
	//
	// // Override any default configs for hard coded networks.
	// switch {
	// case ctx.GlobalBool(TestnetFlag.Name):
	// 	if !ctx.GlobalIsSet(NetworkIdFlag.Name) {
	// 		cfg.NetworkId = 3
	// 	}
	// 	cfg.Genesis = core.DefaultTestnetGenesisBlock()
	// case ctx.GlobalBool(RinkebyFlag.Name):
	// 	if !ctx.GlobalIsSet(NetworkIdFlag.Name) {
	// 		cfg.NetworkId = 4
	// 	}
	// 	cfg.Genesis = core.DefaultRinkebyGenesisBlock()
	// case ctx.GlobalBool(CpchainFlag.Name):
	// 	if !ctx.GlobalIsSet(NetworkIdFlag.Name) {
	// 		cfg.NetworkId = 42
	// 	}
	// 	cfg.Genesis = core.DefaultCpchainGenesisBlock()
	// case ctx.GlobalBool(DeveloperFlag.Name):
	// 	if !ctx.GlobalIsSet(NetworkIdFlag.Name) {
	// 		cfg.NetworkId = 1337
	// 	}
	// 	// Create new developer account or reuse existing one
	// 	var (
	// 		developer accounts.Account
	// 		err       error
	// 	)
	// 	if accs := ks.Accounts(); len(accs) > 0 {
	// 		developer = ks.Accounts()[0]
	// 	} else {
	// 		developer, err = ks.NewAccount("")
	// 		if err != nil {
	// 			Fatalf("Failed to create developer account: %v", err)
	// 		}
	// 	}
	// 	if err := ks.Unlock(developer, ""); err != nil {
	// 		Fatalf("Failed to unlock developer account: %v", err)
	// 	}
	// 	log.Info("Using developer account", "address", developer.Address)
	//
	// 	cfg.Genesis = core.DeveloperGenesisBlock(uint64(ctx.GlobalInt(DeveloperPeriodFlag.Name)), developer.Address)
	// 	if !ctx.GlobalIsSet(GasPriceFlag.Name) {
	// 		cfg.GasPrice = big.NewInt(1)
	// 	}
	// }
	// // TODO(fjl): move trie cache generations into config
	// if gen := ctx.GlobalInt(TrieCacheGenFlag.Name); gen > 0 {
	// 	state.MaxTrieCacheGen = uint16(gen)
	// }
}

func updateNodeConfig(ctx *cli.Context, cfg *node.Config) {
	updateNodeGeneralConfig(ctx, cfg)
	updateP2pConfig(ctx, &cfg.P2P)
	updateRpcConfig(ctx, cfg)
}

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
		if _, err := toml.DecodeFile(path, &cfg); err != nil {
			log.Fatalf("Invalid TOML config file: %v", err)
		}
	}
}

func newConfigNode(ctx *cli.Context) (config, *node.Node) {
	// default
	cfg := config{
		Eth:  eth.DefaultConfig,
		Node: node.DefaultConfig,
	}
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
