package main

import (
	"github.com/urfave/cli"
)

var accountCommand cli.Command

func init() {
	accountFlags := append([]cli.Flag(nil))
	accountCommand = cli.Command{
		Action: showAccount,
		Name:   "account",
		Flags:  accountFlags,
		Usage:  "Show account of cpchain node",
		Before: func(ctx *cli.Context) error {
			return nil
		},
		After: func(ctx *cli.Context) error {
			return nil
		},
	}
}

func showAccount(ctx *cli.Context) error {
	return nil
}
