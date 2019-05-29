package main

import (
	"github.com/urfave/cli"
)

var rnodeCommand cli.Command

func init() {
	rewardFlags := append([]cli.Flag(nil), GasFlags...)
	rnodeCommand = cli.Command{
		Name:  "rnode-quit",
		Flags: wrapperFlags(rewardFlags),
		Usage: "Quit from rnode list",
		Action: quitRnode,
		Description: "Quit from rnode,get lockedDeposit from fundraising account .",
	}
}



func quitRnode(ctx *cli.Context) error {
	console, out, cancel, err := build(ctx)
	if err != nil {
		out.Error(err.Error())
		return nil
	}
	defer cancel()
	err = console.QuitRnode()
	if err != nil {
		out.Fatal(err.Error())
	}
	return nil
}

