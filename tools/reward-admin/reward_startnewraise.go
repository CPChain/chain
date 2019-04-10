package main

import (
	"github.com/urfave/cli"
)

var startnewraiseCommand cli.Command

func init() {
	rewardFlags := append([]cli.Flag(nil))
	startnewraiseCommand = cli.Command{
		Name:   "start-new-raise",
		Flags:  wrapperFlags(rewardFlags),
		Usage:  "Reward contract StartNewRaise",
		Action: startnewraise,
	}
}

func startnewraise(ctx *cli.Context) error {
	admin, out, cancel := Build(ctx)
	defer cancel()
	err := admin.StartNewRaise()
	if err != nil {
		out.Error(err.Error())
	}
	return nil
}
