package main

import (
	"fmt"
	"os"
	"path/filepath"
	"sort"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/tools/contract-admin/admission"
	"bitbucket.org/cpchain/chain/tools/contract-admin/campaign"
	"bitbucket.org/cpchain/chain/tools/contract-admin/congress"
	"bitbucket.org/cpchain/chain/tools/contract-admin/network"
	"bitbucket.org/cpchain/chain/tools/contract-admin/rnode"
	"bitbucket.org/cpchain/chain/tools/contract-admin/rpt"
	"github.com/urfave/cli"
)

func newApp() *cli.App {
	app := cli.NewApp()
	app.Name = filepath.Base(os.Args[0])
	app.Authors = []cli.Author{
		{
			Name:  "The cpchain authors",
			Email: "info@cpchain.io",
		},
	}
	app.Version = configs.Version
	app.Copyright = "LGPL"
	app.Usage = "Executable for the cpchain official contract admin"

	app.Action = cli.ShowAppHelp

	app.Commands = []cli.Command{
		admission.AdmissionCommand,
		campaign.CampaignCommand,
		congress.CongressCommand,
		network.NetworkCommand,
		rnode.RnodeCommand,
		rpt.RptCommand,
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
