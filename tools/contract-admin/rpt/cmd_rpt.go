package rpt

import (
	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"github.com/urfave/cli"
)

var (
	RptCommand = cli.Command{
		Name:  "rpt",
		Usage: "Manage Rpt Contract",
		Description: `
		Manage Rpt Contract
		`,
		Subcommands: []cli.Command{
			{
				Name:        "setlowrptpct",
				Usage:       "set low rpt percentage",
				Action:      setLowRptPercentage,
				Flags:       flags.GeneralFlags,
				Description: `set low rpt percentage`,
			},
			{
				Name:        "settotalseats",
				Usage:       "set total seats",
				Action:      setTotalSeats,
				Flags:       flags.GeneralFlags,
				Description: `set total seats`,
			},
			{
				Name:        "setlowrptseats",
				Usage:       "set low rpt seats",
				Action:      setLowRptSeats,
				Flags:       flags.GeneralFlags,
				Description: `set low rpt seats`,
			},
			{
				Name:        "setwindow",
				Usage:       "set window",
				Action:      setWindow,
				Flags:       flags.GeneralFlags,
				Description: `set window`,
			},
			{
				Name:        "setalpha",
				Usage:       "set alpha",
				Action:      setAlpha,
				Flags:       flags.GeneralFlags,
				Description: `set alpha`,
			},
			{
				Name:        "setbeta",
				Usage:       "set beta",
				Action:      setBeta,
				Flags:       flags.GeneralFlags,
				Description: `set beta`,
			},
			{
				Name:        "setgamma",
				Usage:       "set gamma",
				Action:      setGamma,
				Flags:       flags.GeneralFlags,
				Description: `set gamma`,
			},
			{
				Name:        "setpsi",
				Usage:       "set psi",
				Action:      setPsi,
				Flags:       flags.GeneralFlags,
				Description: `set psi`,
			},
			{
				Name:        "setomega",
				Usage:       "set omega",
				Action:      setOmega,
				Flags:       flags.GeneralFlags,
				Description: `set omega`,
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

func setLowRptPercentage(ctx *cli.Context) error {
	return nil
}

func setTotalSeats(ctx *cli.Context) error {
	return nil
}

func setLowRptSeats(ctx *cli.Context) error {
	return nil
}

func setWindow(ctx *cli.Context) error {
	return nil
}

func setAlpha(ctx *cli.Context) error {
	return nil
}

func setBeta(ctx *cli.Context) error {
	return nil
}

func setGamma(ctx *cli.Context) error {
	return nil
}

func setPsi(ctx *cli.Context) error {
	return nil
}

func setOmega(ctx *cli.Context) error {
	return nil
}

func showConfigs(ctx *cli.Context) error {
	return nil
}
