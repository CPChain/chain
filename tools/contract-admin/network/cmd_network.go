package network

import (
	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"github.com/urfave/cli"
)

var (
	NetworkCommand = cli.Command{
		Name:  "network",
		Usage: "Manage Network Contract",
		Description: `
		Manage Network Contract
		`,
		Flags: flags.GeneralFlags,
		Subcommands: []cli.Command{
			{
				Name:        "sethost",
				Usage:       "set host address",
				Action:      setHost,
				Flags:       flags.GeneralFlags,
				Description: `set host address`,
			},
			{
				Name:        "setcount",
				Usage:       "set count",
				Action:      setCount,
				Flags:       flags.GeneralFlags,
				Description: `set count`,
			},
			{
				Name:        "settimeout",
				Usage:       "set timeout",
				Action:      setTimeout,
				Flags:       flags.GeneralFlags,
				Description: `set timeout`,
			},
			{
				Name:        "setgap",
				Usage:       "set gap",
				Action:      setGap,
				Flags:       flags.GeneralFlags,
				Description: `set gap`,
			},
			{
				Name:        "setopen",
				Usage:       "set open or not",
				Action:      setOpen,
				Flags:       flags.GeneralFlags,
				Description: `set open or nor`,
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

func setHost(ctx *cli.Context) error {
	return nil
}

func setCount(ctx *cli.Context) error {
	return nil
}

func setTimeout(ctx *cli.Context) error {
	return nil
}

func setGap(ctx *cli.Context) error {
	return nil
}

func setOpen(ctx *cli.Context) error {
	return nil
}

func showConfigs(ctx *cli.Context) error {
	return nil
}
