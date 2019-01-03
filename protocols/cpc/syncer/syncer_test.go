package syncer_test

import (
	"fmt"
	"math"
	"math/big"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/protocols/cpc/syncer"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

func TestSyncerNormal(t *testing.T) {
	var (
		n            = 1000
		badIdx       = 0
		p            = NewFakePeer(n, badIdx)
		head, height = p.Head()
	)

	_ = p

	// new a local chain, only genesis block in it
	localchain := newBlockchain(0)

	// create a syncer to sync blocks
	localSyncer := syncer.New(localchain, nil)

	// go sync
	go localSyncer.Synchronise(p, head, height)
	defer localSyncer.Terminate()

	// go fake peer request handle loop
	go p.returnBlocksLoop()
	defer p.quit()

	// act as handleSyncMsg in protocol manager
	for {
		select {

		// received blocks from remote peer, deliever to syncer
		case blocks := <-p.returnCh:

			t.Log("received blocks from peer", len(blocks))

			localSyncer.DeliverBlocks(p.IDString(), blocks)
		}

		// sleep 100 millisecond to wait for syncer processing
		time.Sleep(1000 * time.Millisecond)

		// check localchain status
		num := localchain.CurrentBlock().NumberU64()
		t.Log("updated block chain, latest block number", num)

		// if all blocks synced, return
		if num == uint64(n) {
			return
		}
	}
}

func TestSyncerTimeout(t *testing.T) {

	var (
		n            = 1000
		badIdx       = 0
		p            = NewFakePeer(n, badIdx)
		head, height = p.Head()
	)

	_ = p

	// new a local chain, only genesis block in it
	localchain := newBlockchain(0)

	// create a syncer to sync blocks
	localSyncer := syncer.New(localchain, nil)

	// go sync
	err := localSyncer.Synchronise(p, head, height)

	t.Log("err", err)

	if err != syncer.ErrTimeout {
		t.Fail()
	}

}

func TestSyncerInvalidChain(t *testing.T) {
	var (
		n            = 1000
		badIdx       = 10
		p            = NewFakePeer(n, badIdx)
		head, height = p.Head()
	)

	_ = p

	// new a local chain, only genesis block in it
	localchain := newBlockchain(0)

	// create a syncer to sync blocks
	localSyncer := syncer.New(localchain, nil)

	// go fake peer request handle loop
	go p.returnBlocksLoop()
	defer p.quit()

	// act as handleSyncMsg in protocol manager
	go func() {
		for {
			select {

			// received blocks from remote peer, deliever to syncer
			case blocks := <-p.returnCh:

				t.Log("received blocks from peer", len(blocks))

				localSyncer.DeliverBlocks(p.IDString(), blocks)
			}

			// sleep 100 millisecond to wait for syncer processing
			time.Sleep(1000 * time.Millisecond)

			// check localchain status
			num := localchain.CurrentBlock().NumberU64()
			t.Log("updated block chain, latest block number", num)

			// if all blocks synced, return
			if num == uint64(n) {
				return
			}
		}
	}()

	// go sync
	err := localSyncer.Synchronise(p, head, height)
	defer localSyncer.Terminate()

	t.Log(err)
	if err != syncer.ErrInvalidChain {
		t.Fail()
	}
}

func TestSyncerUnknownPeer(t *testing.T) {
	var (
		n            = 1000
		badIdx       = 0
		p            = NewFakePeer(n, badIdx)
		head, height = p.Head()
	)

	_ = p

	// new a local chain, only genesis block in it
	localchain := newBlockchain(0)

	// create a syncer to sync blocks
	localSyncer := syncer.New(localchain, nil)

	// go fake peer request handle loop
	go p.returnBlocksLoop()
	defer p.quit()

	// act as handleSyncMsg in protocol manager
	go func() {
		for {
			select {

			// received blocks from remote peer, deliever to syncer
			case blocks := <-p.returnCh:

				t.Log("received blocks from peer", len(blocks))

				// invalid peer id when delivering blocks
				err := localSyncer.DeliverBlocks(p.IDString()+"x", blocks)
				if err != syncer.ErrUnknownPeer {
					t.Fail()
				}

				// continue
				err = localSyncer.DeliverBlocks(p.IDString(), blocks)
				if err != nil {
					t.Fail()
				}
			}

			// sleep 100 millisecond to wait for syncer processing
			time.Sleep(1000 * time.Millisecond)

			// check localchain status
			num := localchain.CurrentBlock().NumberU64()
			t.Log("updated block chain, latest block number", num)

			// if all blocks synced, return
			if num == uint64(n) {
				return
			}
		}
	}()

	// go sync
	err := localSyncer.Synchronise(p, head, height)
	defer localSyncer.Terminate()

	t.Log(err)
	if err != nil {
		t.Fail()
	}
}

func TestSyncerSlowPeer(t *testing.T) {
	var (
		n            = 100
		badIdx       = 0
		p            = NewFakePeer(n, badIdx)
		head, height = p.Head()
	)

	_ = p

	// new a local chain, only genesis block in it
	localchain := newBlockchain(200)

	// create a syncer to sync blocks
	localSyncer := syncer.New(localchain, nil)

	// go sync
	err := localSyncer.Synchronise(p, head, height)
	defer localSyncer.Terminate()

	t.Log(err)
	if err != syncer.ErrSlowPeer {
		t.Fail()
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
	_, _ = blockchain.InsertChain(blocks)
	return blockchain
}

type FakePeer struct {
	badBlockIdx int
	blockchain  syncer.BlockChain
	requestCh   chan uint64
	returnCh    chan types.Blocks
	quitCh      chan struct{}
}

func NewFakePeer(n int, badIdx int) *FakePeer {
	return &FakePeer{
		badBlockIdx: badIdx,
		blockchain:  newBlockchain(n),
		requestCh:   make(chan uint64),
		returnCh:    make(chan types.Blocks),
		quitCh:      make(chan struct{}),
	}
}

func (fp *FakePeer) IDString() string {
	return "fake peer"
}

func (fp *FakePeer) Head() (hash common.Hash, ht *big.Int) {
	return fp.blockchain.CurrentBlock().Hash(), fp.blockchain.CurrentBlock().Number()
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
			end := uint64(math.Min(float64(start+syncer.MaxBlockFetch), float64(number.Uint64()+1)))
			blocks := make(types.Blocks, int(end-start))

			fmt.Println("received start request", "start", start, "batch", syncer.MaxBlockFetch, "end", end)
			for i := start; i < end; i++ {
				block := fp.blockchain.GetBlockByNumber(i)
				if fp.badBlockIdx == int(i) {
					// change its parent hash to generate a bad block

					block.RefHeader().ParentHash = common.Hash{}
				}
				blocks[i-start] = block
			}

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
