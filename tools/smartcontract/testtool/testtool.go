// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package main

import (
	"context"
	"fmt"
	"log"
	"os"
	"sort"

	"bitbucket.org/cpchain/chain/api/cpclient"
	"github.com/ethereum/go-ethereum/common"
	"github.com/urfave/cli"
)

const (
	ENDPOINT = "endpoint"
)

func main() {
	app := cli.NewApp()
	app.Usage = "executable command tool for easy test"
	app.Flags = []cli.Flag{
		cli.StringFlag{
			Name:  ENDPOINT + ",ep",
			Value: "http://127.0.0.1:8521",
			Usage: "endpoint like http://127.0.0.1:8521",
		},
	}

	app.Commands = []cli.Command{
		{
			Name:    "get_block_number",
			Aliases: []string{"bn"},
			Usage:   "get block number",
			Action: func(c *cli.Context) error {
				endpoint := c.GlobalString(ENDPOINT)
				client, err := cpclient.Dial(endpoint)
				if err != nil {
					log.Fatal(err.Error())
				}
				blockNumber := client.GetBlockNumber()
				fmt.Println(blockNumber)
				return nil
			},
		},
		{
			Name:    "balance",
			Aliases: []string{"bal"},
			Usage:   "get balance by address. \n\t\texample: ./testtool bal ${addr}",
			Action: func(c *cli.Context) error {
				endpoint := c.GlobalString(ENDPOINT)
				client, err := cpclient.Dial(endpoint)
				if err != nil {
					log.Fatal(err.Error())
				}
				balance, _ := client.BalanceAt(context.Background(), common.HexToAddress(c.Args().First()), nil)
				fmt.Println(balance)
				return nil
			},
		},
	}

	sort.Sort(cli.FlagsByName(app.Flags))
	sort.Sort(cli.CommandsByName(app.Commands))

	err := app.Run(os.Args)
	if err != nil {
		log.Fatal(err)
	}
}
