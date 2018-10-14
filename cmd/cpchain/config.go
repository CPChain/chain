package main

import (
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/eth"
	"bitbucket.org/cpchain/chain/node"
	"github.com/BurntSushi/toml"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/urfave/cli"
	"os"
	"path/filepath"
)

type config struct {
	Eth  eth.Config
	Node node.Config
}

func updateGeneralConfig(ctx *cli.Context, cfg *node.Config) {
	// no need.  only create a subdirectory for testnet, etc.
}

func updateP2pConfig(ctx *cli.Context, cfg *p2p.Config) {
}

// TODO @sangh
func updateRpcConfig(ctx *cli.Context, cfg *node.Config) {
}

func updateChainConfig(ctx *cli.Context, cfg *eth.Config) {
}

func updateNodeConfig(ctx *cli.Context, cfg *node.Config) {
	updateGeneralConfig(ctx, cfg)
	updateP2pConfig(ctx, &cfg.P2P)
	updateRpcConfig(ctx, cfg)
}

func updateConfigFromCli(ctx *cli.Context, cfg *config) {
	updateNodeConfig(ctx, &cfg.Node)
	updateChainConfig(ctx, &cfg.Eth)
}


// Returns a config merged from
// - default config,
// - --config file or sys default
// - the command line
func getConfig(ctx *cli.Context) config {
	// default
	cfg := config{
		Eth:  eth.DefaultConfig,
		Node: node.DefaultConfig,
	}

	// --config
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

	// command line
	updateConfigFromCli(ctx, &cfg)
	return cfg
}
