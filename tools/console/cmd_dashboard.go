package main

import (
	"github.com/urfave/cli"
)

var dashboardCommand cli.Command

func init() {
	dashboardFlags := append([]cli.Flag(nil))
	dashboardCommand = cli.Command{
		Action: showDashboard,
		Name:   "dashboard",
		Flags:  dashboardFlags,
		Usage:  "Show dashboard of cpchain node",
		Before: func(ctx *cli.Context) error {
			return nil
		},
		After: func(ctx *cli.Context) error {
			return nil
		},
	}
}

func showDashboard(ctx *cli.Context) error {
	return nil
}
