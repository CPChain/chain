package main

import (
	"context"
	"fmt"
	"math/big"

	"bitbucket.org/cpchain/chain/cmd/cpchain/campaign/common"
	"bitbucket.org/cpchain/chain/cmd/cpchain/campaign/manager"
	"bitbucket.org/cpchain/chain/cmd/cpchain/campaign/output"
	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/configs"
	"github.com/urfave/cli"
)

var campaignCommand cli.Command

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

	if ctx.IsSet(flags.RunModeFlagName) {
		runMode := configs.RunMode(ctx.String(flags.RunModeFlagName))
		configs.SetRunMode(runMode)
	}

	manager.SetGasConfig(price, limit)
	manager.SetRunMode(configs.GetRunMode())

	_ctx, cancel := context.WithCancel(context.Background())
	console, err := manager.NewConsole(&_ctx, rpc, kspath, pwdfile, &out)
	return console, &out, cancel, err
}

func init() {
	campaignFlags := append([]cli.Flag(nil))
	stopCampaignFlags := append([]cli.Flag(nil), flags.GasFlags...)
	campaignCommand = cli.Command{
		Name:  "campaign",
		Flags: campaignFlags,
		Usage: "Manage campaign",
		Subcommands: []cli.Command{
			{
				Name:        "start",
				Usage:       "Start claiming campaign",
				Flags:       flags.WrapperFlags(campaignFlags),
				Action:      startCampaign,
				Description: fmt.Sprintf(`Start Mining`),
			},
			{
				Name:        "stop",
				Usage:       "Stop claiming campaign",
				Flags:       flags.WrapperFlags(stopCampaignFlags),
				Action:      stopCampaign,
				Description: fmt.Sprintf(`Stop Mining`),
			},
			{
				Action: showStatus,
				Name:   "status",
				Flags:  flags.WrapperFlags(campaignFlags),
				Usage:  "Show status of cpchain node",
			},
		},
	}
}

func startCampaign(ctx *cli.Context) error {
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

func stopCampaign(ctx *cli.Context) error {
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
