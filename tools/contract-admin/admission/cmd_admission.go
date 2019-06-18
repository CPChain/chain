package admission

import (
	"fmt"

	"github.com/urfave/cli"
)

var (
	AdmissionCommand = cli.Command{
		Name:  "admission",
		Usage: "Manage Admission Contract",
		Description: `
		Manage Admission Contract
		`,
		Subcommands: []cli.Command{
			{
				Name:        "setcpu",
				Usage:       "set cpu difficulty",
				Action:      setCPUDifficulty,
				Flags:       []cli.Flag{},
				Description: `set cpu difficulty`,
			},
			{
				Name:        "setmem",
				Usage:       "set memory difficulty",
				Action:      setMemDifficulty,
				Flags:       []cli.Flag{},
				Description: `set memory difficulty`,
			},
			{
				Name:        "show",
				Usage:       "Show CPU difficulty and memory difficulty",
				Action:      showDifficulties,
				Flags:       []cli.Flag{},
				Description: `show cpu difficulty and memory difficulty`,
			},
		},
	}
)

func setCPUDifficulty(ctx *cli.Context) error {
	fmt.Println(ctx.Args().Get(0))
	return nil
}

func setMemDifficulty(ctx *cli.Context) error {
	return nil
}

func showDifficulties(ctx *cli.Context) error {
	return nil
}
