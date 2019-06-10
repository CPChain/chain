package main

import (
	"context"
	"fmt"
	"math/big"

	"bitbucket.org/cpchain/chain/cmd/cpchain/console/common"
	"bitbucket.org/cpchain/chain/cmd/cpchain/console/manager"
	"bitbucket.org/cpchain/chain/cmd/cpchain/console/output"
	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"github.com/urfave/cli"
)

var MinerCommand cli.Command

func build(ctx *cli.Context) (*manager.Console, common.Output, context.CancelFunc, error) {
	rpc, kspath, pwdfile, err := flags.Validator(ctx)
	out := output.NewLogOutput()
	if err != nil {
		return nil, &out, nil, err
	}

	var price *big.Int = nil
	if ctx.IsSet("gasprice") {
		price = new(big.Int).SetUint64(ctx.Uint64("gasprice"))
	}

	var limit uint64 = 2000000
	if ctx.IsSet("gaslimit") {
		limit = ctx.Uint64("gaslimit")
	}

	manager.SetGasConfig(price, limit)

	_ctx, cancel := context.WithCancel(context.Background())
	console, err := manager.NewConsole(&_ctx, rpc, kspath, pwdfile, &out)
	if err != nil {
		out.Fatal(err.Error())
	}
	return console, &out, cancel, err
}

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
				Flags:       flags.WrapperFlags(minerFlags),
				Action:      startMining,
				Description: fmt.Sprintf(`Start Mining`),
			},
			{
				Name:        "stop",
				Usage:       "Stop claiming campaign",
				Flags:       flags.WrapperFlags(minerFlags),
				Action:      stopMining,
				Description: fmt.Sprintf(`Stop Mining`),
			},
			{
				Action: showStatus,
				Name:   "status",
				Flags:  flags.WrapperFlags(minerFlags),
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
