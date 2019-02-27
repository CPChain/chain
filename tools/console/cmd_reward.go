package main

import (
	"fmt"
	"math/big"

	"bitbucket.org/cpchain/chain/configs"

	"github.com/urfave/cli"
)

var rewardCommand cli.Command

func init() {
	rewardFlags := append([]cli.Flag(nil), GasFlags...)
	withdrawFlags := append(rewardFlags, cli.Int64Flag{
		Name:  "value",
		Usage: "Value, default 0 cpc",
	})
	rewardCommand = cli.Command{
		Name:  "reward",
		Flags: rewardFlags,
		Usage: "Manage reward contract",
		Subcommands: []cli.Command{
			{
				Name:        "deposit",
				Usage:       "submit deposit",
				Flags:       wrapperFlags(rewardFlags),
				Action:      deposit,
				Description: fmt.Sprintf(`Submit Deposit`),
			},
			{
				Name:        "withdraw",
				Usage:       "withdraw",
				Flags:       wrapperFlags(withdrawFlags),
				Action:      withdraw,
				Description: fmt.Sprintf(`Withdraw`),
			},
			{
				Name:        "wantrenew",
				Usage:       "want renew",
				Flags:       wrapperFlags(rewardFlags),
				Action:      wantRenew,
				Description: fmt.Sprintf(`Want Renew`),
			},
			{
				Name:        "quitrenew",
				Usage:       "quit renew",
				Flags:       wrapperFlags(rewardFlags),
				Action:      quitRenew,
				Description: fmt.Sprintf(`Quit Renew`),
			},
		},
		Before: func(ctx *cli.Context) error {
			// gasprice := ctx.Int64("gasprice")
			// gaslimit := ctx.Int64("gaslimit")
			return nil
		},
		After: func(ctx *cli.Context) error {
			return nil
		},
	}
}

func deposit(ctx *cli.Context) error {
	console, out, cancel := build(ctx)
	defer cancel()
	err := console.SubmitDeposit()
	if err != nil {
		out.Error(err.Error())
	}
	return nil
}

func withdraw(ctx *cli.Context) error {
	console, out, cancel := build(ctx)
	defer cancel()
	value := ctx.Int64("value")
	err := console.Withdraw(new(big.Int).Mul(big.NewInt(value), big.NewInt(configs.Cpc)))
	if err != nil {
		out.Error(err.Error())
	}
	return nil
}

func wantRenew(ctx *cli.Context) error {
	console, out, cancel := build(ctx)
	defer cancel()
	err := console.WantRenew()
	if err != nil {
		out.Error(err.Error())
	}
	return nil
}

func quitRenew(ctx *cli.Context) error {
	console, out, cancel := build(ctx)
	defer cancel()
	err := console.QuitRenew()
	if err != nil {
		out.Error(err.Error())
	}
	return nil
}
