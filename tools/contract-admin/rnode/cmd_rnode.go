package rnode

import (
	"github.com/urfave/cli"
)

var (
	RnodeCommand = cli.Command{
		Name:  "rnode",
		Usage: "Manage Rnode Contract",
		Description: `
		Manage Rnode Contract
		`,
		Subcommands: []cli.Command{
			{
				Name:        "setthreshold",
				Usage:       "set threshold ",
				Action:      setThreshold,
				Flags:       []cli.Flag{},
				Description: `set threshold`,
			},
			{
				Name:        "setperiod",
				Usage:       "set period",
				Action:      setPeriod,
				Flags:       []cli.Flag{},
				Description: `set period`,
			},
			{
				Name:        "setversion",
				Usage:       "set version",
				Action:      setVersion,
				Flags:       []cli.Flag{},
				Description: `set version`,
			},
			{
				Name:        "refund",
				Usage:       "refund",
				Action:      refund,
				Flags:       []cli.Flag{},
				Description: `refund`,
			},
			{
				Name:        "refundall",
				Usage:       "refund all",
				Action:      refundAll,
				Flags:       []cli.Flag{},
				Description: `refund all`,
			},
			{
				Name:        "disable",
				Usage:       "disable rnode contract",
				Action:      disable,
				Flags:       []cli.Flag{},
				Description: `disable rnode contract`,
			},
			{
				Name:        "isrnode",
				Usage:       "is rnode",
				Action:      isRnode,
				Flags:       []cli.Flag{},
				Description: `check an address is rnode`,
			},
			{
				Name:        "showconfigs",
				Usage:       "show configs in contract",
				Action:      showConfigs,
				Flags:       []cli.Flag{},
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
