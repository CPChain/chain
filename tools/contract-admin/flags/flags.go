// Copyright 2018 The cpchain authors
// This file is part of cpchain.
//
// cpchain is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// cpchain is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with cpchain. If not, see <http://www.gnu.org/licenses/>.

package flags

import (
	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/urfave/cli"
)

var flagMap = make(map[string]cli.Flag)

func init() {
	cli.VersionFlag = cli.BoolFlag{
		Name:  "version, v",
		Usage: "Print the version",
	}

	cli.HelpFlag = cli.BoolFlag{
		Name:  "help, h",
		Usage: "Show help",
	}

	Register(GeneralFlags...)
}

func Register(flags ...cli.Flag) {
	for _, flag := range flags {
		if _, ok := flagMap[flag.GetName()]; ok {
			log.Fatalf("Flag already exists: %v", flag.GetName())
		}
		flagMap[flag.GetName()] = flag
	}
}

func GetByName(name string) cli.Flag {
	flag, ok := flagMap[name]
	if !ok {
		log.Fatalf("Flag does not exist: %v", name)
	}
	return flag
}

// begin flags

const (
	KeystorePath = "keystore"
	Endpoint     = "endpoint"
	ContractAddr = "contractaddr"
)

var GeneralFlags = []cli.Flag{
	cli.StringFlag{
		Name:  KeystorePath,
		Usage: "Keystore file path for contract admin",
	},
	cli.StringFlag{
		Name:  Endpoint,
		Usage: "Endpoint to interact with",
	},
	cli.StringFlag{
		Name:  ContractAddr,
		Usage: "Contract address",
	},
}
