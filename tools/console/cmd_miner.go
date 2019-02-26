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
				Flags:       wrapperFlags(minerFlags),
				Action:      startMining,
				Description: fmt.Sprintf(`Start Mining`),
			},
			{
				Name:        "stop",
				Usage:       "stop mining",
				Flags:       wrapperFlags(minerFlags),
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
	console, out, cancel := build(ctx)
	defer cancel()
	err := console.StartMining()
	if err != nil {
		out.Error(err.Error())
	}
	return nil
}

func stopMining(ctx *cli.Context) error {
	console, out, cancel := build(ctx)
	defer cancel()
	err := console.StopMining()
	if err != nil {
		out.Error(err.Error())
	}
	return nil
}
