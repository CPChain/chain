package main

import (
	"os"

	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/naoina/toml"
	"github.com/urfave/cli"
)

var (
	dumpConfigCommand = cli.Command{
		Action:      dumpConfig,
		Name:        "dumpconfig",
		Usage:       "Show configuration values",
		ArgsUsage:   "",
		Description: `The dumpconfig command shows configuration values.`,
	}
)

func dumpConfig(ctx *cli.Context) error {
	cfg, _ := newConfigNode(ctx)
	err := toml.NewEncoder(os.Stdout).Encode(cfg)
	if err != nil {
		log.Fatalf("Encoding config to TOML failed: %v", err)
	}
	return nil
}
