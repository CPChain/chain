package main

import (
	"fmt"

	"github.com/urfave/cli"
)

var MinerCommand cli.Command

func init() {
	minerFlags := append([]cli.Flag(nil))
	MinerCommand = cli.Command{
		Name:  "campaign",
		Flags: minerFlags,
		Usage: "Manage campaign",
		Subcommands: []cli.Command{
			{
				Name:        "start",
				Usage:       "Start claiming campaign",
				Flags:       wrapperFlags(minerFlags),
				Action:      startMining,
				Description: fmt.Sprintf(`Start Mining`),
			},
			{
				Name:        "stop",
				Usage:       "Stop claiming campaign",
				Flags:       wrapperFlags(minerFlags),
				Action:      stopMining,
				Description: fmt.Sprintf(`Stop Mining`),
			},
			{
				Action: showStatus,
				Name:   "status",
				Flags:  wrapperFlags(minerFlags),
				Usage:  "Show status of cpchain node",
			},
		},
	}
}

func startMining(ctx *cli.Context) error {
	console, out, cancel, err := build(ctx)
	if err != nil {
		out.Error(err.Error())
		return nil
	}
	defer cancel()
	err = console.StartMining()
	if err != nil {
		out.Error(err.Error())
		return nil
	}
	return nil
}

func stopMining(ctx *cli.Context) error {
	console, out, cancel, err := build(ctx)
	if err != nil {
		out.Error(err.Error())
		return nil
	}
	defer cancel()
	err = console.StopMining()
	if err != nil {
		out.Error(err.Error())
		return nil
	}
	return nil
}

func showStatus(ctx *cli.Context) error {
	console, out, cancel, err := build(ctx)
	if err != nil {
		out.Error(err.Error())
		return nil
	}
	defer cancel()
	status, err := console.GetStatus()
	if err != nil {
		out.Error(err.Error())
		return nil
	}
	out.Status(status)
	return nil
}
