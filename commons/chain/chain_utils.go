package chainutils

import (
	"compress/gzip"
	"fmt"
	"io"
	"os"
	"os/signal"
	"strings"
	"syscall"

	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/eth"
	"bitbucket.org/cpchain/chain/ethdb"
	"bitbucket.org/cpchain/chain/node"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common/fdlimit"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/urfave/cli"
)

const (
	importBatchSize = 2500
)

// MakeChainDatabase open an LevelDB using the flags passed to the client and will hard crash if it fails.
func MakeChainDatabase(ctx *cli.Context, stack *node.Node, databaseCache int) ethdb.Database {
	var (
		handles = makeDatabaseHandles()
	)
	name := "chaindata"

	chainDb, err := stack.OpenDatabase(name, databaseCache, handles)
	if err != nil {
		log.Fatalf("Could not open database: %v", err)
	}
	return chainDb
}

// MakeGenesis builds a genesis block object.
func MakeGenesis(ctx *cli.Context) *core.Genesis {
	return core.DefaultCpchainGenesisBlock()
}

// OpenOrMakeChain creates a chain manager from set command line flags.
func OpenOrMakeChain(ctx *cli.Context, stack *node.Node, databaseCache int, trieCache int) (chain *core.BlockChain, chainDb ethdb.Database) {
	var err error
	chainDb = MakeChainDatabase(ctx, stack, databaseCache)

	config, _, err := core.SetupGenesisBlock(chainDb, MakeGenesis(ctx))
	if err != nil {
		log.Fatalf("%v", err)
	}
	var engine consensus.Engine
	engine = dpor.New(config.Dpor, chainDb)

	gcmode := "full"
	if ctx.IsSet(flags.GCModeFlagName) {
		gcmode = ctx.String(flags.GCModeFlagName)
		if gcmode != "full" && gcmode != "archive" {
			log.Fatalf("--%s must be either 'full' or 'archive'", flags.GCModeFlagName)
		}
	}
	cacheCfg := &core.CacheConfig{
		Disabled:      gcmode == "archive",
		TrieNodeLimit: eth.DefaultConfig.TrieCache,
		TrieTimeLimit: eth.DefaultConfig.TrieTimeout,
	}
	cacheCfg.TrieNodeLimit = trieCache

	vmcfg := vm.Config{EnablePreimageRecording: false} // TODO: consider if add VMEnableDebugFlag {AC}
	rsaKey, _ := stack.RsaKey()
	chain, err = core.NewBlockChain(chainDb, cacheCfg, config, engine, vmcfg, nil, rsaKey.PrivateKey) // TODO: give a fake or real RemoteDB
	if err != nil {
		log.Fatalf("Can't create BlockChain: %v", err)
	}
	return chain, chainDb
}

// makeDatabaseHandles raises out the number of allowed file handles per process
// for Geth and returns half of the allowance to assign to the database.
func makeDatabaseHandles() int {
	limit, err := fdlimit.Current()
	if err != nil {
		log.Fatalf("Failed to retrieve file descriptor allowance: %v", err)
	}
	if limit < 2048 {
		if err := fdlimit.Raise(2048); err != nil {
			log.Fatalf("Failed to raise file descriptor allowance: %v", err)
		}
	}
	if limit > 2048 { // cap database file descriptors even if more is available
		limit = 2048
	}
	return limit / 2 // Leave half for networking and other stuff
}

func ImportChain(chain *core.BlockChain, fn string) error {
	// Watch for Ctrl-C while the import is running.
	// If a signal is received, the import will stop at the next batch.
	interrupt := make(chan os.Signal, 1)
	stop := make(chan struct{})
	signal.Notify(interrupt, syscall.SIGINT, syscall.SIGTERM)
	defer signal.Stop(interrupt)
	defer close(interrupt)
	go func() {
		if _, ok := <-interrupt; ok {
			log.Info("Interrupted during import, stopping at next batch")
		}
		close(stop)
	}()
	checkInterrupt := func() bool {
		select {
		case <-stop:
			return true
		default:
			return false
		}
	}

	log.Info("Importing blockchain", "file", fn)

	// Open the file handle and potentially unwrap the gzip stream
	fh, err := os.Open(fn)
	if err != nil {
		return err
	}
	defer fh.Close()

	var reader io.Reader = fh
	if strings.HasSuffix(fn, ".gz") {
		if reader, err = gzip.NewReader(reader); err != nil {
			return err
		}
	}
	stream := rlp.NewStream(reader, 0)

	// Run actual the import.
	blocks := make(types.Blocks, importBatchSize)
	n := 0
	for batch := 0; ; batch++ {
		// Load a batch of RLP blocks.
		if checkInterrupt() {
			return fmt.Errorf("interrupted")
		}
		i := 0
		for ; i < importBatchSize; i++ {
			var b types.Block
			if err := stream.Decode(&b); err == io.EOF {
				break
			} else if err != nil {
				return fmt.Errorf("at block %d: %v", n, err)
			}
			// don't import first block
			if b.NumberU64() == 0 {
				i--
				continue
			}
			blocks[i] = &b
			n++
		}
		if i == 0 {
			break
		}
		// Import the batch.
		if checkInterrupt() {
			return fmt.Errorf("interrupted")
		}
		missing := missingBlocks(chain, blocks[:i])
		if len(missing) == 0 {
			log.Info("Skipping batch as all blocks present", "batch", batch, "first", blocks[0].Hash(), "last", blocks[i-1].Hash())
			continue
		}
		if _, err := chain.InsertChain(missing); err != nil {
			return fmt.Errorf("invalid block %d: %v", n, err)
		}
	}
	return nil
}

func missingBlocks(chain *core.BlockChain, blocks []*types.Block) []*types.Block {
	head := chain.CurrentBlock()
	for i, block := range blocks {
		// If we're behind the chain head, only check block, state is available at head
		if head.NumberU64() > block.NumberU64() {
			if !chain.HasBlock(block.Hash(), block.NumberU64()) {
				return blocks[i:]
			}
			continue
		}
		// If we're above the chain head, state availability is a must
		if !chain.HasBlockAndState(block.Hash(), block.NumberU64()) {
			return blocks[i:]
		}
	}
	return nil
}

// ExportChain exports a blockchain into the specified file, truncating any data
// already present in the file.
func ExportChain(blockchain *core.BlockChain, fn string) error {
	log.Info("Exporting blockchain", "file", fn)

	// Open the file handle and potentially wrap with a gzip stream
	fh, err := os.OpenFile(fn, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, os.ModePerm)
	if err != nil {
		return err
	}
	defer fh.Close()

	var writer io.Writer = fh
	if strings.HasSuffix(fn, ".gz") {
		writer = gzip.NewWriter(writer)
		defer writer.(*gzip.Writer).Close()
	}
	// Iterate over the blocks and export them
	if err := blockchain.Export(writer); err != nil {
		return err
	}
	log.Info("Exported blockchain", "file", fn)

	return nil
}

// ExportAppendChain exports a blockchain into the specified file, appending to
// the file if data already exists in it.
func ExportAppendChain(blockchain *core.BlockChain, fn string, first uint64, last uint64) error {
	log.Info("Exporting blockchain", "file", fn)

	// Open the file handle and potentially wrap with a gzip stream
	fh, err := os.OpenFile(fn, os.O_CREATE|os.O_APPEND|os.O_WRONLY, os.ModePerm)
	if err != nil {
		return err
	}
	defer fh.Close()

	var writer io.Writer = fh
	if strings.HasSuffix(fn, ".gz") {
		writer = gzip.NewWriter(writer)
		defer writer.(*gzip.Writer).Close()
	}
	// Iterate over the blocks and export them
	if err := blockchain.ExportN(writer, first, last); err != nil {
		return err
	}
	log.Info("Exported blockchain to", "file", fn)
	return nil
}

// TODO: ADD UNITTESTS {AC}
