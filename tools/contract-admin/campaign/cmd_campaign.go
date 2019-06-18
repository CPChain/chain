package campaign

import (
	"github.com/urfave/cli"
)

var (
	CampaignCommand = cli.Command{
		Name:  "campaign",
		Usage: "Manage Campaign Contract",
		Description: `
		Manage Campaign Contract
		`,
		Subcommands: []cli.Command{
			{
				Name:        "setadmissionaddr",
				Usage:       "set admission contract address",
				Action:      setAdmissionAddress,
				Flags:       []cli.Flag{},
				Description: `set admission contract address`,
			},
			{
				Name:        "setrnodeaddr",
				Usage:       "set rnode contract address",
				Action:      setRnodeAddress,
				Flags:       []cli.Flag{},
				Description: `set rnode contract address`,
			},
			{
				Name:        "setminnoc",
				Usage:       "set min noc",
				Action:      setMinNoc,
				Flags:       []cli.Flag{},
				Description: `set rnode contract address`,
			},
			{
				Name:        "setmaxnoc",
				Usage:       "set max noc",
				Action:      setMaxNoc,
				Flags:       []cli.Flag{},
				Description: `set rnode contract address`,
			},
			{
				Name:        "showconfigs",
				Usage:       "show configs in contract",
				Action:      showConfigs,
				Flags:       []cli.Flag{},
				Description: `show configs in contract`,
			},
			{
				Name:        "showcandidates",
				Usage:       "show candidates in contract in given term range",
				Action:      showCandidates,
				Flags:       []cli.Flag{},
				Description: `show candidates in contract in given term range in contract`,
			},
		},
	}
)

func setAdmissionAddress(ctx *cli.Context) error {
	return nil
}

func setRnodeAddress(ctx *cli.Context) error {
	return nil
}

func setMinNoc(ctx *cli.Context) error {
	return nil
}

func setMaxNoc(ctx *cli.Context) error {
	return nil
}

func setAcceptableBlocks(ctx *cli.Context) error {
	return nil
}

func setVersion(ctx *cli.Context) error {
	return nil
}

func showConfigs(ctx *cli.Context) error {
	return nil
}

func showCandidates(ctx *cli.Context) error {
	return nil
}
