package main

import (
	"github.com/urfave/cli"
)

var statusCommand cli.Command

// TODO : 是否在锁定期，是，可续投压钱；否，不可续投不可压钱

func init() {
	statusFlags := append([]cli.Flag(nil))
	statusCommand = cli.Command{
		Action: showStatus,
		Name:   "status",
		Flags:  wrapperFlags(statusFlags),
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
	console, out, cancel := build(ctx)
	defer cancel()
	status, err := console.GetStatus()
	if err != nil {
		out.Error(err.Error())
	}
	out.Status(status)
	return nil
}
