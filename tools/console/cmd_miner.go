package main

import (
	"fmt"

	"github.com/urfave/cli"
)

var minerCommand cli.Command

func init() {
	minerFlags := append([]cli.Flag(nil))
	minerCommand = cli.Command{
		Name:  "miner",
		Flags: minerFlags,
		Usage: "Manage miner",
		Subcommands: []cli.Command{
			{
				Name:        "start",
				Usage:       "Start mining",
				Flags:       append([]cli.Flag(nil)),
				Action:      startMining,
				Description: fmt.Sprintf(`Start Mining`),
			},
			{
				Name:        "stop",
				Usage:       "stop mining",
				Flags:       append([]cli.Flag(nil)),
				Action:      stopMining,
				Description: fmt.Sprintf(`Stop Mining`),
			},
		},
		Before: func(ctx *cli.Context) error {
			return nil
		},
		After: func(ctx *cli.Context) error {
			return nil
		},
	}
}

func startMining(ctx *cli.Context) error {
	return nil
}

func stopMining(ctx *cli.Context) error {
	return nil
}
