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

package main

import (
	"bufio"
	"bytes"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"sync/atomic"
	"time"

	"bitbucket.org/cpchain/chain/cmd/cpchain/commons"
	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/contracts/dpor/primitive_register"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/state"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/trie"
	"github.com/naoina/toml"
	"github.com/syndtr/goleveldb/leveldb/util"
	"github.com/urfave/cli"
)

var defaultGenesisPath = filepath.Join(flags.GetByName(flags.DataDirFlagName).(cli.StringFlag).Value, "genesis.toml")

var chainCommand = cli.Command{
	Name:  "chain",
	Usage: "Manage blockchain",
	Subcommands: []cli.Command{
		{
			Name:  "init",
			Usage: "Bootstrap and initialize a new genesis block",
			Flags: append([]cli.Flag{
				flags.GetByName(flags.DataDirFlagName),
				flags.GetByName(flags.RunModeFlagName),
			}, flags.LogFlags...),
			Action:    initChain,
			ArgsUsage: "[/path/to/genesis.toml]",
			Description: fmt.Sprintf(`The default genesis file path is: %v.
If no genesis file is found, the initialization is aborted.`, defaultGenesisPath),
		},
		{
			Name:  "cleandb",
			Usage: "Clean blockchain and state databases",
			Flags: append([]cli.Flag{
				flags.GetByName(flags.DataDirFlagName),
			}, flags.LogFlags...),
			Action:      cleanDB,
			ArgsUsage:   " ",
			Description: `Remove blockchain and state databases`,
		},
		{
			Action:    importChain,
			Name:      "import",
			Usage:     "Import a blockchain file",
			ArgsUsage: "<filename>",
			Flags: append([]cli.Flag{
				flags.GetByName(flags.DataDirFlagName),
				flags.GetByName(flags.NoCompactionFlagName),
				flags.GetByName(flags.CacheFlagName),
				flags.GetByName(flags.CacheDatabaseFlagName),
				flags.GetByName(flags.CacheGCFlagName),
			}, flags.LogFlags...),
			Description: `The import command imports blocks from an RLP-encoded form. The form can be one file
with several RLP-encoded blocks, or several files can be used.

If only one file is used, import error will result in failure. If several files are used,
processing will proceed even if an individual RLP-file import failure occurs.`,
		},
		{
			Action:    exportChain,
			Name:      "export",
			Usage:     "Export blockchain into file",
			ArgsUsage: "<output file> [blockNumFirst blockNumLast]",
			Flags: append([]cli.Flag{
				flags.GetByName(flags.DataDirFlagName),
				flags.GetByName(flags.CacheFlagName),
				flags.GetByName(flags.CacheDatabaseFlagName),
				flags.GetByName(flags.CacheGCFlagName),
			}, flags.LogFlags...),
			Description: `Requires a first argument of the file to write to.
Optional second and third arguments control the first and
last block to write. In this mode, the file will be appended
if already existing.`,
		},
		{
			Action:    importPreimages,
			Name:      "import-preimages",
			Usage:     "Import the preimage database from an RLP stream",
			ArgsUsage: "<datafile>",
			Flags: append([]cli.Flag{
				flags.GetByName(flags.DataDirFlagName),
				flags.GetByName(flags.CacheFlagName),
				flags.GetByName(flags.CacheDatabaseFlagName),
				flags.GetByName(flags.CacheGCFlagName),
			}, flags.LogFlags...),
			Description: `The import-preimages command imports hash preimages from an RLP encoded stream.`,
		},
		{
			Action:    exportPreimages,
			Name:      "export-preimages",
			Usage:     "Export the preimage database into an RLP stream",
			ArgsUsage: "<dumpfile>",
			Flags: append([]cli.Flag{
				flags.GetByName(flags.DataDirFlagName),
				flags.GetByName(flags.CacheFlagName),
				flags.GetByName(flags.CacheDatabaseFlagName),
				flags.GetByName(flags.CacheGCFlagName),
			}, flags.LogFlags...),
			Description: `The export-preimages command export hash preimages to an RLP encoded stream`,
		},
		{
			Action:    dump,
			Name:      "dump",
			Usage:     "Dump a specific block from storage",
			ArgsUsage: "<blockHash | blockNum> [blockHash | blockNum]...",
			Flags: append([]cli.Flag{
				flags.GetByName(flags.DataDirFlagName),
				flags.GetByName(flags.CacheFlagName),
				flags.GetByName(flags.CacheDatabaseFlagName),
				flags.GetByName(flags.CacheGCFlagName),
			}, flags.LogFlags...),
			Description: `The arguments are interpreted as block numbers or hashes.
Use "cpchain chain dump 0" to dump the genesis block.`,
		},
		{
			Action: compactDB,
			Name:   "compact",
			Usage:  "Compact the database in datadir/cpchain/chaindata directory",
			Flags: append([]cli.Flag{
				flags.GetByName(flags.DataDirFlagName),
			}, flags.LogFlags...),
			Description: ``,
		},
		{
			Action:    deletePattern,
			Name:      "delete",
			Usage:     "Delete those key-values contains the substring",
			ArgsUsage: "<substring>",
			Flags: append([]cli.Flag{
				flags.GetByName(flags.DataDirFlagName),
			}, flags.LogFlags...),

			Description: "Example: ./cpchain chain delete dpor- --datadir ~/.cpchain",
		},
	},
}

// initChain creates a genesis block from a toml format file
func initChain(ctx *cli.Context) error {
	// Make sure we have a valid genesis TOML and run with suitable runmode.
	genesisPath := ctx.Args().First()
	var genesis *core.Genesis

	if ctx.IsSet(flags.RunModeFlagName) {
		_ = configs.SetRunMode(configs.RunMode(ctx.String(flags.RunModeFlagName)))
	}
	log.Info("runMode", "runMode", configs.GetRunMode())

	if len(genesisPath) == 0 {
		genesis = core.DefaultGenesisBlock()
	} else {
		file, err := os.Open(genesisPath)
		if err != nil {
			log.Fatalf("Failed to read genesis file: %v", err)
		}
		defer file.Close()

		genesis = new(core.Genesis)
		if err := toml.NewDecoder(file).Decode(genesis); err != nil {
			log.Fatalf("invalid genesis file: %v", err)
		}
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
	log.Info("Successfully wrote genesis state", "database", name, "hash", hash.Hex())
	return nil
}

func cleanDB(ctx *cli.Context) {
	_, node := newConfigNode(ctx)

	name := configs.DatabaseName
	// Ensure the database exists in the first place
	logger := log.New("database", name)

	// create a path name under the instance dir
	dbdir := node.ResolvePath(name)
	if !common.FileExist(dbdir) {
		logger.Info("Database doesn't exist, skipping", "path", dbdir)
		return
	}
	// Confirm removal and execute
	fmt.Println(dbdir)
	fmt.Print("Remove this database? [y/N]")
	rd := bufio.NewReader(os.Stdin)
	input, err := rd.ReadString('\n')
	if err != nil {
		logger.Fatalf("%v", err)
	}
	input = strings.ToUpper(strings.TrimRight(input, "\r\n"))
	confirm := input == "Y"
	switch {
	case !confirm:
		logger.Info("Database deletion aborted")
	default:
		start := time.Now()
		os.RemoveAll(dbdir)
		logger.Info("Database successfully deleted", "elapsed", common.PrettyDuration(time.Since(start)))
	}
}

func importChain(ctx *cli.Context) error {
	if len(ctx.Args()) != 1 {
		log.Fatalf("This command requires a single argument for the imported file")
	}

	log.Info("Begin import")
	cfg, node := newConfigNode(ctx)

	primitive_register.RegisterPrimitiveContracts()
	chain, chainDb := commons.OpenChain(ctx, node, &cfg.Cpc)
	defer chainDb.Close()

	// Start periodically gathering memory profiles
	var peakMemAlloc, peakMemSys uint64
	go func() {
		stats := new(runtime.MemStats)
		for {
			runtime.ReadMemStats(stats)
			if atomic.LoadUint64(&peakMemAlloc) < stats.Alloc {
				atomic.StoreUint64(&peakMemAlloc, stats.Alloc)
			}
			if atomic.LoadUint64(&peakMemSys) < stats.Sys {
				atomic.StoreUint64(&peakMemSys, stats.Sys)
			}
			time.Sleep(5 * time.Second)
		}
	}()
	// Import the chain
	start := time.Now()

	if err := commons.ImportChain(chain, ctx.Args().First()); err != nil {
		log.Error("Import error", "err", err)
	}
	// flush the caches
	chain.Stop()

	fmt.Printf("Import done in %v.\n\n", time.Since(start))

	// Output pre-compaction stats mostly to see the import trashing
	db := chainDb.(*database.LDBDatabase)

	stats, err := db.LDB().GetProperty("leveldb.stats")
	if err != nil {
		log.Fatalf("Failed to read database stats: %v", err)
	}
	fmt.Println(stats)

	ioStats, err := db.LDB().GetProperty("leveldb.iostats")
	if err != nil {
		log.Fatalf("Failed to read database iostats: %v", err)
	}
	fmt.Println(ioStats)

	fmt.Printf("Trie cache misses:  %d\n", trie.CacheMisses())
	fmt.Printf("Trie cache unloads: %d\n\n", trie.CacheUnloads())

	// Print the memory statistics used by the importing
	mem := new(runtime.MemStats)
	runtime.ReadMemStats(mem)

	fmt.Printf("Object memory: %.3f MB current, %.3f MB peak\n", float64(mem.Alloc)/1024/1024, float64(atomic.LoadUint64(&peakMemAlloc))/1024/1024)
	fmt.Printf("System memory: %.3f MB current, %.3f MB peak\n", float64(mem.Sys)/1024/1024, float64(atomic.LoadUint64(&peakMemSys))/1024/1024)
	fmt.Printf("Allocations:   %.3f million\n", float64(mem.Mallocs)/1000000)
	fmt.Printf("GC pause:      %v\n\n", time.Duration(mem.PauseTotalNs))

	if ctx.IsSet(flags.NoCompactionFlagName) {
		return nil
	}

	// Compact the entire database to more accurately measure disk io and print the stats
	start = time.Now()
	fmt.Println("Compacting entire database...")
	if err = db.LDB().CompactRange(util.Range{}); err != nil {
		log.Fatalf("Compaction failed: %v", err)
	}
	fmt.Printf("Compaction done in %v.\n\n", time.Since(start))

	stats, err = db.LDB().GetProperty("leveldb.stats")
	if err != nil {
		log.Fatalf("Failed to read database stats: %v", err)
	}
	fmt.Println(stats)

	ioStats, err = db.LDB().GetProperty("leveldb.iostats")
	if err != nil {
		log.Fatalf("Failed to read database iostats: %v", err)
	}
	fmt.Println(ioStats)

	return nil
}

func exportChain(ctx *cli.Context) error {
	argcnt := len(ctx.Args())
	if argcnt != 1 && argcnt != 3 {
		log.Fatal("Wrong number of arguments specified.")
	}
	cfg, node := newConfigNode(ctx)

	chain, _ := commons.OpenChain(ctx, node, &cfg.Cpc)
	start := time.Now()

	var err error
	fp := ctx.Args().First()

	if argcnt == 1 {
		err = commons.ExportChainN(chain, fp, uint64(0), chain.CurrentBlock().NumberU64())
	} else {
		// This can be improved to allow for numbers larger than 9223372036854775807
		first, ferr := strconv.ParseInt(ctx.Args().Get(1), 10, 64)
		last, lerr := strconv.ParseInt(ctx.Args().Get(2), 10, 64)
		if ferr != nil || lerr != nil {
			log.Fatal("Export error in parsing parameters: block number not an integer")
		}
		if first < 0 || last < 0 {
			log.Fatal("Export error: block number must be greater than 0")
		}
		err = commons.ExportChainN(chain, fp, uint64(first), uint64(last))
	}

	if err != nil {
		log.Fatalf("Export error: %v\n", err)
	}
	fmt.Printf("Export done in %v\n", time.Since(start))
	return nil
}

// importPreimages imports preimage data from the specified file.
func importPreimages(ctx *cli.Context) error {
	if len(ctx.Args()) < 1 {
		log.Fatalf("This command requires an argument.")
	}
	cfg, stack := newConfigNode(ctx)
	diskdb := commons.MakeChainDatabase(ctx, stack, cfg.Cpc.DatabaseCache).(*database.LDBDatabase)

	start := time.Now()
	if err := commons.ImportPreimages(diskdb, ctx.Args().First()); err != nil {
		log.Fatalf("Import error: %v\n", err)
	}
	fmt.Printf("Import done in %v\n", time.Since(start))
	return nil
}

// exportPreimages dumps the preimage data to specified json file in streaming way.
func exportPreimages(ctx *cli.Context) error {
	if len(ctx.Args()) < 1 {
		log.Fatal("This command requires an argument.")
	}
	cfg, stack := newConfigNode(ctx)
	diskdb := commons.MakeChainDatabase(ctx, stack, cfg.Cpc.DatabaseCache).(*database.LDBDatabase)

	start := time.Now()
	if err := commons.ExportPreimages(diskdb, ctx.Args().First()); err != nil {
		log.Fatalf("Export error: %v\n", err)
	}
	fmt.Printf("Export done in %v\n", time.Since(start))
	return nil
}

// dump outputs specified blocks from storage
func dump(ctx *cli.Context) error {
	if len(ctx.Args()) < 1 {
		log.Fatal("This command requires an argument.")
	}

	cfg, stack := newConfigNode(ctx)
	chain, chainDb := commons.OpenChain(ctx, stack, &cfg.Cpc)
	for _, arg := range ctx.Args() {
		var block *types.Block
		if hashish(arg) {
			block = chain.GetBlockByHash(common.HexToHash(arg))
		} else {
			num, _ := strconv.Atoi(arg)
			block = chain.GetBlockByNumber(uint64(num))
		}
		if block == nil {
			fmt.Println("{}")
			log.Fatalf("block not found")
		} else {
			state, err := state.New(block.StateRoot(), state.NewDatabase(chainDb))
			if err != nil {
				log.Fatalf("could not create new state: %v", err)
			}
			fmt.Printf("%s\n", state.Dump())
		}
	}
	chainDb.Close()
	return nil
}

func compactDB(ctx *cli.Context) (err error) {
	if len(ctx.Args()) != 0 {
		log.Fatal("This command requires no argument.")
	}

	cfg, stack := newConfigNode(ctx)
	_, chainDb := commons.OpenChain(ctx, stack, &cfg.Cpc)
	defer chainDb.Close()

	if db, ok := chainDb.(*database.LDBDatabase); ok {
		log.Warn("This requires a few minutes to finish, please do not interrupt!")
		err = db.LDB().CompactRange(util.Range{})
		if err == nil {
			log.Warn("Successfully compacted the underlying database!")
		}
	}

	return err
}

func deletePattern(ctx *cli.Context) (err error) {
	if len(ctx.Args()) != 1 {
		log.Fatal("This command requires argument <delete-key-substring>.")
	}

	cfg, stack := newConfigNode(ctx)
	_, chainDb := commons.OpenChain(ctx, stack, &cfg.Cpc)
	defer chainDb.Close()

	if db, ok := chainDb.(*database.LDBDatabase); ok {
		iter := db.LDB().NewIterator(nil, nil)

		log.Warn("This requires a few minutes to finish, please do not interrupt!")

		for iter.Next() {
			key := iter.Key()

			// if matches, delete
			if bytes.Contains(key, []byte(ctx.Args()[0])) {
				err = db.Delete(key)
				if err != nil {
					log.Error("Error occurs when deleting key", "key", key)
				}
			}
		}
		iter.Release()
		err = iter.Error()

		log.Warn("Finished deleting!")
	}

	return err
}

// hashish returns true for strings that look like hashes.
func hashish(x string) bool {
	_, err := strconv.Atoi(x)
	return err != nil
}
