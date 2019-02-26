package main

import (
	"github.com/urfave/cli"
)

var statusCommand cli.Command

func init() {
	statusFlags := append([]cli.Flag(nil))
	statusCommand = cli.Command{
		Action: showStatus,
		Name:   "status",
		Flags:  statusFlags,
		Usage:  "Show status of cpchain node",
		Before: func(ctx *cli.Context) error {
			return nil
		},
		After: func(ctx *cli.Context) error {
			return nil
		},
	}
}

func showStatus(ctx *cli.Context) error {
	return nil
}
