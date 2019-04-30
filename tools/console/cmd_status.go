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
		Flags:  wrapperFlags(statusFlags),
		Usage:  "Show status of cpchain node",
	}
}

func showStatus(ctx *cli.Context) error {
	console, out, cancel, err := build(ctx)
	if err != nil {
		out.Error(err.Error())
		return nil
	}
	defer cancel()
	status, err := console.GetStatus()
	if err != nil {
		out.Error(err.Error())
		return nil
	}
	out.Status(status)
	return nil
}
