package main

import (
	"fmt"

	"github.com/urfave/cli"
)

var rewardCommand cli.Command

func init() {
	rewardFlags := append([]cli.Flag(nil))
	rewardCommand = cli.Command{
		Name:  "reward",
		Flags: rewardFlags,
		Usage: "Manage reward contract",
		Subcommands: []cli.Command{
			{
				Name:        "deposit",
				Usage:       "submit deposit",
				Flags:       append([]cli.Flag(nil)),
				Action:      deposit,
				Description: fmt.Sprintf(`Submit Deposit`),
			},
			{
				Name:        "withdraw",
				Usage:       "withdraw",
				Flags:       append([]cli.Flag(nil)),
				Action:      withdraw,
				Description: fmt.Sprintf(`Withdraw`),
			},
			{
				Name:        "wantrenew",
				Usage:       "want renew",
				Flags:       append([]cli.Flag(nil)),
				Action:      wantRenew,
				Description: fmt.Sprintf(`Want Renew`),
			},
			{
				Name:        "quitrenew",
				Usage:       "quit renew",
				Flags:       append([]cli.Flag(nil)),
				Action:      quitRenew,
				Description: fmt.Sprintf(`Quit Renew`),
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

func deposit(ctx *cli.Context) error {
	return nil
}

func withdraw(ctx *cli.Context) error {
	return nil
}

func wantRenew(ctx *cli.Context) error {
	return nil
}

func quitRenew(ctx *cli.Context) error {
	return nil
}
