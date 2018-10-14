package main

import (
	"fmt"
	"path/filepath"

	"bitbucket.org/cpchain/chain/cmd/flags"
	"github.com/urfave/cli"
)

var defaultGenesisPath = filepath.Join(flags.GetByName("datadir").(cli.StringFlag).Value, "genesis.toml")

var chainCommand = cli.Command{
	Name:  "chain",
	Usage: "Manage blockchain",
	Flags: []cli.Flag{
		flags.GetByName("datadir"),
		flags.GetByName("keystore"),
	},
	Subcommands: []cli.Command{
		{
			Name:      "init",
			Usage:     "Init the genesis block",
			Action:    initChain,
			ArgsUsage: "[path/to/genesis.toml]",
			Description: fmt.Sprintf(`The default genesis file path is: %v.
If no genesis file is found, the initialization is aborted.`, defaultGenesisPath),
		},
	},
}

// create a genesis block from a toml format file
func initChain(ctx *cli.Context) error {
	path := defaultGenesisPath
	if ctx.NArg() > 0 {
		path = ctx.Args().First()
	}
	// test if the file exists
	fmt.Println(path)

	return nil
}

// func initGenesis(ctx *cli.Context) error {
// 	// Make sure we have a valid genesis JSON
// 	genesisPath := ctx.Args().First()
//
// 	if len(genesisPath) == 0 {
// 		utils.Fatalf("Must supply path to genesis JSON file")
// 	}
// 	file, err := os.Open(genesisPath)
// 	if err != nil {
// 		utils.Fatalf("Failed to read genesis file: %v", err)
// 	}
// 	defer file.Close()
//
// 	genesis := new(core.Genesis)
// 	if err := json.NewDecoder(file).Decode(genesis); err != nil {
// 		utils.Fatalf("invalid genesis file: %v", err)
// 	}
// 	// Open an initialise both full and light databases
// 	stack := makeFullNode(ctx)
// 	for _, name := range []string{"chaindata", "lightchaindata"} {
// 		chaindb, err := stack.OpenDatabase(name, 0, 0)
// 		if err != nil {
// 			utils.Fatalf("Failed to open database: %v", err)
// 		}
// 		_, hash, err := core.SetupGenesisBlock(chaindb, genesis)
// 		if err != nil {
// 			utils.Fatalf("Failed to write genesis block: %v", err)
// 		}
// 		log.Info("Successfully wrote genesis state", "database", name, "hash", hash)
// 	}
// 	return nil
// }
