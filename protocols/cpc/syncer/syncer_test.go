package syncer_test

import (
	"fmt"
	"math"
	"math/big"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/protocols/cpc/syncer"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

func init() {
	log.SetLevel(log.DebugLevel)
}

func TestSyncerNormal(t *testing.T) {
	var (
		n            = 1000
		p            = NewFakePeer(n)
		head, height = p.Head()
	)

	_ = p

	// new a local chain, only genesis block in it
	localchain := newBlockchain(0)

	// create a syncer to sync blocks
	localSyncer := syncer.New(localchain, nil)

	// go sync
	go localSyncer.Synchronise(p, head, height)

	// go fake peer request handle loop
	go p.returnBlocksLoop()

	// act as handleSyncMsg in protocol manager
	for {
		select {

		// received blocks from remote peer, deliever to syncer
		case blocks := <-p.returnCh:

			fmt.Println("received blocks from peer", len(blocks))

			localSyncer.DeliverBlocks(p.ID(), blocks)
		}

		// sleep 100 millisecond to wait for syncer processing
		time.Sleep(1000 * time.Millisecond)

		// check localchain status
		num := localchain.CurrentBlock().NumberU64()
		fmt.Println("updated block chain, latest block number", num)

		// if all blocks synced, return
		if num == uint64(n) {
			return
		}
	}
}

func newBlockchain(n int) syncer.BlockChain {
	db := database.NewMemDatabase()
	remoteDB := database.NewIpfsDbWithAdapter(database.NewFakeIpfsAdapter())
	gspec := core.DefaultGenesisBlock()
	genesis := gspec.MustCommit(db)
	config := gspec.Config
	dporConfig := config.Dpor
	dporFakeEngine := dpor.NewFaker(dporConfig, db)
	blocks, _ := core.GenerateChain(config, genesis, dporFakeEngine, db, remoteDB, n, nil)
	blockchain, _ := core.NewBlockChain(db, nil, gspec.Config, dporFakeEngine, vm.Config{}, remoteDB, nil)
	_, err := blockchain.InsertChain(blocks)
	fmt.Println("err when inserting chain", err)
	return blockchain
}

type FakePeer struct {
	blocks     types.Blocks
	blockchain syncer.BlockChain
	requestCh  chan uint64
	returnCh   chan types.Blocks
	quitCh     chan struct{}
}

func NewFakePeer(n int) *FakePeer {
	return &FakePeer{
		blockchain: newBlockchain(n),
		requestCh:  make(chan uint64),
		returnCh:   make(chan types.Blocks),
		quitCh:     make(chan struct{}),
	}
}

func (fp *FakePeer) ID() string {
	return "test peer"
}

func (fp *FakePeer) Head() (hash common.Hash, ht *big.Int) {
	return fp.blockchain.CurrentBlock().Hash(), fp.blockchain.CurrentBlock().Number()
}

func (fp *FakePeer) SetHead(hash common.Hash, ht *big.Int) {
	panic("not implemented")
}

func (fp *FakePeer) SendGetBlocks(start uint64) error {
	fp.requestCh <- start
	return nil
}

func (fp *FakePeer) returnBlocksLoop() {
	for {
		select {
		case start := <-fp.requestCh:
			_, number := fp.Head()
			end := uint64(math.Min(float64(start+syncer.MaxBlockFetch), float64(number.Uint64())))
			blocks := make(types.Blocks, int(end-start+1))

			fmt.Println("received start request", "start", start, "batch", syncer.MaxBlockFetch, "end", end)
			for i := start; i <= end; i++ {
				fmt.Println("retrieved block", "i", i)
				block := fp.blockchain.GetBlockByNumber(i)
				blocks[i-start] = block
			}
			fmt.Println("len of blocks", len(blocks))

			fp.returnCh <- blocks

		case <-fp.quitCh:
			return
		}
	}
}

func (fp *FakePeer) quit() {
	if fp.quitCh != nil {
		close(fp.quitCh)
	}
}
