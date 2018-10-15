package main

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"time"

	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/core"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/console"
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
		{
			Name:     "cleandb",
			Usage:    "Clean blockchain and state databases",
			Category: "BLOCKCHAIN COMMANDS",
			Flags: []cli.Flag{
				flags.GetByName("datadir"),
			},
			Action:    cleanDB,
			ArgsUsage: " ",
			Description: `
Remove blockchain and state databases`,
		},
	},
}

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

func cleanDB(ctx *cli.Context) error {
	_, node := newConfigNode(ctx)

	for _, name := range []string{"chaindata", "lightchaindata"} {
		// Ensure the database exists in the first place
		logger := log.New("database", name)

		dbdir := node.ResolvePath(name)
		if !common.FileExist(dbdir) {
			logger.Info("Database doesn't exist, skipping", "path", dbdir)
			continue
		}
		// Confirm removal and execute
		fmt.Println(dbdir)
		confirm, err := console.Stdin.PromptConfirm("Remove this database?")
		switch {
		case err != nil:
			logger.Fatalf("%v", err)
		case !confirm:
			logger.Warn("Database deletion aborted")
		default:
			start := time.Now()
			os.RemoveAll(dbdir)
			logger.Info("Database successfully deleted", "elapsed", common.PrettyDuration(time.Since(start)))
		}
	}
	return nil
}
