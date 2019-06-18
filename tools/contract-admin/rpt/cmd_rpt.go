package rpt

import (
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
				Flags:       []cli.Flag{},
				Description: `set low rpt percentage`,
			},
			{
				Name:        "settotalseats",
				Usage:       "set total seats",
				Action:      setTotalSeats,
				Flags:       []cli.Flag{},
				Description: `set total seats`,
			},
			{
				Name:        "setlowrptseats",
				Usage:       "set low rpt seats",
				Action:      setLowRptSeats,
				Flags:       []cli.Flag{},
				Description: `set low rpt seats`,
			},
			{
				Name:        "setwindow",
				Usage:       "set window",
				Action:      setWindow,
				Flags:       []cli.Flag{},
				Description: `set window`,
			},
			{
				Name:        "setalpha",
				Usage:       "set alpha",
				Action:      setAlpha,
				Flags:       []cli.Flag{},
				Description: `set alpha`,
			},
			{
				Name:        "setbeta",
				Usage:       "set beta",
				Action:      setBeta,
				Flags:       []cli.Flag{},
				Description: `set beta`,
			},
			{
				Name:        "setgamma",
				Usage:       "set gamma",
				Action:      setGamma,
				Flags:       []cli.Flag{},
				Description: `set gamma`,
			},
			{
				Name:        "setpsi",
				Usage:       "set psi",
				Action:      setPsi,
				Flags:       []cli.Flag{},
				Description: `set psi`,
			},
			{
				Name:        "setomega",
				Usage:       "set omega",
				Action:      setOmega,
				Flags:       []cli.Flag{},
				Description: `set omega`,
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
