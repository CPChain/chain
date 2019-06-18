package rnode

import (
	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"github.com/urfave/cli"
)

var (
	RnodeCommand = cli.Command{
		Name:  "rnode",
		Usage: "Manage Rnode Contract",
		Description: `
		Manage Rnode Contract
		`,
		Flags: flags.GeneralFlags,
		Subcommands: []cli.Command{
			{
				Name:        "setthreshold",
				Usage:       "set threshold ",
				Action:      setThreshold,
				Flags:       flags.GeneralFlags,
				Description: `set threshold`,
			},
			{
				Name:        "setperiod",
				Usage:       "set period",
				Action:      setPeriod,
				Flags:       flags.GeneralFlags,
				Description: `set period`,
			},
			{
				Name:        "setversion",
				Usage:       "set version",
				Action:      setVersion,
				Flags:       flags.GeneralFlags,
				Description: `set version`,
			},
			{
				Name:        "refund",
				Usage:       "refund",
				Action:      refund,
				Flags:       flags.GeneralFlags,
				Description: `refund`,
			},
			{
				Name:        "refundall",
				Usage:       "refund all",
				Action:      refundAll,
				Flags:       flags.GeneralFlags,
				Description: `refund all`,
			},
			{
				Name:        "disable",
				Usage:       "disable rnode contract",
				Action:      disable,
				Flags:       flags.GeneralFlags,
				Description: `disable rnode contract`,
			},
			{
				Name:        "isrnode",
				Usage:       "is rnode",
				Action:      isRnode,
				Flags:       flags.GeneralFlags,
				Description: `check an address is rnode`,
			},
			{
				Name:        "showconfigs",
				Usage:       "show configs in contract",
				Action:      showConfigs,
				Flags:       flags.GeneralFlags,
				Description: `show configs in contract`,
			},
		},
	}
)

func setThreshold(ctx *cli.Context) error {
	return nil
}

func setPeriod(ctx *cli.Context) error {
	return nil
}

func setVersion(ctx *cli.Context) error {
	return nil
}

func refund(ctx *cli.Context) error {
	return nil
}

func refundAll(ctx *cli.Context) error {
	return nil
}

func disable(ctx *cli.Context) error {
	return nil
}

func isRnode(ctx *cli.Context) error {
	return nil
}

func showConfigs(ctx *cli.Context) error {
	return nil
}
