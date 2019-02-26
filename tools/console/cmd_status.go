package main

import (
	"context"

	"bitbucket.org/cpchain/chain/tools/console/manager"
	"bitbucket.org/cpchain/chain/tools/console/output"
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
		Before: func(ctx *cli.Context) error {
			return nil
		},
		After: func(ctx *cli.Context) error {
			return nil
		},
	}
}

func showStatus(ctx *cli.Context) error {
	rpc, kspath, pwdfile, err := validator(ctx)
	out := output.NewLogOutput()
	if err != nil {
		out.Fatal(err.Error())
	}
	_ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	console := manager.NewConsole(&_ctx, rpc, kspath, pwdfile, &out)
	status, err := console.GetStatus()
	if err != nil {
		out.Error(err.Error())
	}
	out.Status(status)
	return nil
}
