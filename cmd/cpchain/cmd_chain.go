package main

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"

	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/core"
	"github.com/urfave/cli"
)

var defaultGenesisPath = filepath.Join(flags.GetByName("datadir").(cli.StringFlag).Value, "genesis.toml")

var chainCommand = cli.Command{
	Name:  "chain",
	Usage: "Manage blockchain",
	Subcommands: []cli.Command{
		{
			Name:     "init",
			Usage:    "Bootstrap and initialize a new blockchain with genesis block",
			Category: "BLOCKCHAIN COMMANDS",
			Flags: []cli.Flag{
				flags.GetByName("datadir"),
			},
			Action:    initChain,
			ArgsUsage: "[/path/to/genesis.toml]",
			Description: fmt.Sprintf(`The default genesis file path is: %v.
If no genesis file is found, the initialization is aborted.`, defaultGenesisPath),
		},
	},
}

// // temporary usage
// // sample func to update from ctx
// func getConfigWorkaround(ctx *cli.Context) config {
// 	cfg := getConfig(ctx)
//
// 	// update it here
//
// 	// use it somewhere
// 	return cfg
// }

// initChain creates a genesis block from a toml format file
func initChain(ctx *cli.Context) error {
	// Make sure we have a valid genesis JSON.
	genesisPath := ctx.Args().First()
	if len(genesisPath) == 0 {
		log.Fatal("Must supply path to genesis JSON file")
	}
	file, err := os.Open(genesisPath)
	if err != nil {
		log.Fatalf("Failed to read genesis file: %v", err)
	}
	defer file.Close()

	genesis := new(core.Genesis)
	if err := json.NewDecoder(file).Decode(genesis); err != nil {
		log.Fatalf("invalid genesis file: %v", err)
	}
	// Intialize database.
	_, node := newConfigNode(ctx)
	name := configs.DatabaseName
	chaindb, err := node.OpenDatabase(name, 0, 0)
	if err != nil {
		log.Fatalf("Failed to open database: %v", err)
	}
	_, hash, err := core.SetupGenesisBlock(chaindb, genesis)
	if err != nil {
		log.Fatalf("Failed to write genesis block: %v", err)
	}
	log.Info("Successfully wrote genesis state", "database", name, "hash", hash)
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
