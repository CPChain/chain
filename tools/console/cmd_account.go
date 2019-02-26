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
		Flags:  wrapperFlags(accountFlags),
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
	console, out, cancel := build(ctx)
	defer cancel()
	balance, err := console.GetBalance()
	if err != nil {
		out.Error(err.Error())
	}
	out.Balance(balance)
	return nil
}
