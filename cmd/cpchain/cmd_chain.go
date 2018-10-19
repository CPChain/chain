package main

import (
	"bufio"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"sync/atomic"
	"time"

	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/commons/chain"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/ethdb"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/trie"
	"github.com/naoina/toml"
	"github.com/syndtr/goleveldb/leveldb/util"
	"github.com/urfave/cli"
)

var defaultGenesisPath = filepath.Join(flags.GetByName("datadir").(cli.StringFlag).Value, "genesis.toml")

var chainCommand = cli.Command{
	Name:  "chain",
	Usage: "Manage blockchain",
	Subcommands: []cli.Command{
		{
			Name:  "init",
			Usage: "Bootstrap and initialize a new genesis block",
			Flags: []cli.Flag{
				flags.GetByName("datadir"),
			},
			Action:    initChain,
			ArgsUsage: "[/path/to/genesis.toml]",
			Description: fmt.Sprintf(`The default genesis file path is: %v.
If no genesis file is found, the initialization is aborted.`, defaultGenesisPath),
		},
		{
			Name:  "cleandb",
			Usage: "Clean blockchain and state databases",
			Flags: []cli.Flag{
				flags.GetByName(flags.DataDirFlagName),
			},
			Action:    cleanDB,
			ArgsUsage: " ",
			Description: `
Remove blockchain and state databases`,
		},
		{
			Action:    importChain,
			Name:      "import",
			Usage:     "Import a blockchain file",
			ArgsUsage: "<filename>",
			Flags: []cli.Flag{
				flags.GetByName(flags.DataDirFlagName),
				flags.GetByName(flags.NoCompactionFlagName),
				flags.GetByName(flags.CacheFlagName),
				flags.GetByName(flags.CacheDatabaseFlagName),
				flags.GetByName(flags.CacheGCFlagName),
			},
			Description: `
The import command imports blocks from an RLP-encoded form. The form can be one file
with several RLP-encoded blocks, or several files can be used.

If only one file is used, import error will result in failure. If several files are used,
processing will proceed even if an individual RLP-file import failure occurs.`,
		},
		{
			Action:    exportChain,
			Name:      "export",
			Usage:     "Export blockchain into file",
			ArgsUsage: "<output file> [blockNumFirst blockNumLast]",
			Flags: []cli.Flag{
				flags.GetByName(flags.DataDirFlagName),
				flags.GetByName(flags.CacheFlagName),
			},
			Description: `Requires a first argument of the file to write to.
Optional second and third arguments control the first and
last block to write. In this mode, the file will be appended
if already existing.`,
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
	// Make sure we have a valid genesis TOML.
	genesisPath := ctx.Args().First()
	var genesis *core.Genesis
	if len(genesisPath) == 0 {
		genesis = core.DefaultCpchainGenesisBlock()
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
	if len(ctx.Args()) < 1 {
		log.Fatalf("This command requires an argument.")
	}
	if len(ctx.Args()) > 1 {
		log.Fatalf("This command can only import a single file.")
	}
	cfg, node := newConfigNode(ctx)
	dbCache := cfg.Eth.DatabaseCache
	trieCache := cfg.Eth.TrieCache
	chain, chainDb := chainutils.OpenChain(ctx, node, dbCache, trieCache)
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

	if err := chainutils.ImportChain(chain, ctx.Args().First()); err != nil {
		log.Error("Import error", "err", err)
	}
	chain.Stop()
	fmt.Printf("Import done in %v.\n\n", time.Since(start))

	// Output pre-compaction stats mostly to see the import trashing
	db := chainDb.(*ethdb.LDBDatabase)

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
	if len(ctx.Args()) < 1 {
		log.Fatalf("This command requires an argument.")
	}
	cfg, node := newConfigNode(ctx)
	dbCache := cfg.Eth.DatabaseCache
	trieCache := cfg.Eth.TrieCache
	chain, _ := chainutils.OpenChain(ctx, node, dbCache, trieCache)
	start := time.Now()

	var err error
	fp := ctx.Args().First()
	if len(ctx.Args()) < 3 {
		err = chainutils.ExportChain(chain, fp)
	} else {
		// This can be improved to allow for numbers larger than 9223372036854775807
		first, ferr := strconv.ParseInt(ctx.Args().Get(1), 10, 64)
		last, lerr := strconv.ParseInt(ctx.Args().Get(2), 10, 64)
		if ferr != nil || lerr != nil {
			log.Fatalf("Export error in parsing parameters: block number not an integer\n")
		}
		if first < 0 || last < 0 {
			log.Fatalf("Export error: block number must be greater than 0\n")
		}
		err = chainutils.ExportAppendChain(chain, fp, uint64(first), uint64(last))
	}

	if err != nil {
		log.Fatalf("Export error: %v\n", err)
	}
	fmt.Printf("Export done in %v\n", time.Since(start))
	return nil
}
