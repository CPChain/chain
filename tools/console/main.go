package main

import (
	"fmt"
	"os"
	"path/filepath"
	"sort"

	"bitbucket.org/cpchain/chain/configs"
	"github.com/urfave/cli"
)

func newApp() *cli.App {
	app := cli.NewApp()
	// the executable name
	app.Name = filepath.Base(os.Args[0])
	app.Authors = []cli.Author{
		{
			Name:  "The cpchain authors",
			Email: "info@cpchain.io",
		},
	}
	app.Version = configs.Version
	app.Copyright = "LGPL"
	app.Usage = "Command-line tool for the cpchain node management"
	// be fair to the fish shell.
	// app.EnableBashCompletion = true

	app.Action = cli.ShowAppHelp

	app.Commands = []cli.Command{
		statusCommand,
		minerCommand,
		rnodeCommand,
	}

	// maintain order
	sort.Sort(cli.CommandsByName(app.Commands))

	return app
}

func main() {
	if err := newApp().Run(os.Args); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
