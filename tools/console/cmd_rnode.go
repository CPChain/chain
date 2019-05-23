package main

import (
	"github.com/urfave/cli"
)

var rnodeCommand cli.Command

func init() {
	rewardFlags := append([]cli.Flag(nil), GasFlags...)
	rnodeCommand = cli.Command{
		Name:  "rnode",
		Flags: wrapperFlags(rewardFlags),
		Usage: "Manage to join or quit rnode",
		Action: quitRnode,
		Subcommands: []cli.Command{
			{
				Name:        "join",
				Usage:       "Join in rnode list",
				Flags:       wrapperFlags(rewardFlags),
				Description: "If this account have enough money,default transfer 200000 ether to fundraising account .",
				Action:      joinRnode,
			},
			{
				Name:        "quit",
				Usage:       "Quit from rnode list",
				Flags:       wrapperFlags(rewardFlags),
				Description: "Quit from rnode,get lockedDeposit from fundraising account .",
				Action:      quitRnode,
			},


		},
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

func joinRnode(ctx *cli.Context) error {
	console, out, cancel, err := build(ctx)
	if err != nil {
		out.Error(err.Error())
		return nil
	}
	defer cancel()

	err = console.JoinRnode()
	if err != nil {
		out.Fatal(err.Error())
	}
	return nil
}
