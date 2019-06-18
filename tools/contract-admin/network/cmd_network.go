package network

import (
	"github.com/urfave/cli"
)

var (
	NetworkCommand = cli.Command{
		Name:  "network",
		Usage: "Manage Network Contract",
		Description: `
		Manage Network Contract
		`,
		Subcommands: []cli.Command{
			{
				Name:        "sethost",
				Usage:       "set host address",
				Action:      setHost,
				Flags:       []cli.Flag{},
				Description: `set host address`,
			},
			{
				Name:        "setcount",
				Usage:       "set count",
				Action:      setCount,
				Flags:       []cli.Flag{},
				Description: `set count`,
			},
			{
				Name:        "settimeout",
				Usage:       "set timeout",
				Action:      setTimeout,
				Flags:       []cli.Flag{},
				Description: `set timeout`,
			},
			{
				Name:        "setgap",
				Usage:       "set gap",
				Action:      setGap,
				Flags:       []cli.Flag{},
				Description: `set gap`,
			},
			{
				Name:        "setopen",
				Usage:       "set open or not",
				Action:      setOpen,
				Flags:       []cli.Flag{},
				Description: `set open or nor`,
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
