package main

import (
	"github.com/urfave/cli"
)

var startnewroundCommand cli.Command

func init() {
	rewardFlags := append([]cli.Flag(nil))
	startnewroundCommand = cli.Command{
		Name:   "start-new-round",
		Flags:  wrapperFlags(rewardFlags),
		Usage:  "Reward contract StartNewRound",
		Action: startnewround,
	}
}

func startnewround(ctx *cli.Context) error {
	admin, out, cancel := Build(ctx)
	defer cancel()
	err := admin.StartNewRound()
	if err != nil {
		out.Error(err.Error())
	}
	return nil
}
