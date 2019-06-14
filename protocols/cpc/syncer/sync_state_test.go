package syncer_test

import (
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/protocols/cpc/syncer"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/trie"
)

// makeTestTrie create a sample test trie to test node-wise reconstruction.
func makeTestTrie(db database.Database) (*trie.Database, *trie.Trie, map[string][]byte) {
	// Create an empty trie
	triedb := trie.NewDatabase(db)
	trie, _ := trie.New(common.Hash{}, triedb)

	// Fill it with some arbitrary data
	content := make(map[string][]byte)
	for i := byte(0); i < 255; i++ {
		// Map the same data under multiple keys
		key, val := common.LeftPadBytes([]byte{1, i}, 32), []byte{i}
		content[string(key)] = val
		trie.Update(key, val)

		key, val = common.LeftPadBytes([]byte{2, i}, 32), []byte{i}
		content[string(key)] = val
		trie.Update(key, val)

		// Add some other data to inflate the trie
		for j := byte(3); j < 13; j++ {
			key, val = common.LeftPadBytes([]byte{j, i}, 32), []byte{j, i}
			content[string(key)] = val
			trie.Update(key, val)
		}
	}
	trie.Commit(nil)

	// Return the generated trie
	return triedb, trie, content
}

func TestSyncState(t *testing.T) {
	var (
		batch   = 1
		numbers = 100
		peer    = NewFakePeer(numbers, 0, false)
	)

	stateRoot := peer.blockchain.CurrentBlock().StateRoot()

	diskdb := database.NewMemDatabase()

	blockchain := newBlockchainWithExistsDB(0, false, diskdb)

	// triedb := trie.NewDatabase(diskdb)
	sched := trie.NewSync(stateRoot, diskdb, nil)

	go peer.returnBlocksLoop()
	defer peer.quit()

	queue := append([]common.Hash{}, sched.Missing(batch)...)
	t.Log("diskdb keys len", len(diskdb.Keys()))
	for len(queue) > 0 {
		results := make([]trie.SyncResult, len(queue))
		for i, hash := range queue {
			go peer.RequestNodeData([]common.Hash{hash})
			data := <-peer.returnStateDataCh
			results[i] = trie.SyncResult{Hash: hash, Data: data[0]}
		}
		if _, index, err := sched.Process(results); err != nil {
			t.Fatalf("failed to process result #%d: %v", index, err)
		}
		if index, err := sched.Commit(diskdb); err != nil {
			t.Fatalf("failed to commit data #%d: %v", index, err)
		}
		queue = append(queue[:0], sched.Missing(batch)...)
	}
	t.Log("diskdb keys len", len(diskdb.Keys()))

	stateDB, err := blockchain.StateAt(stateRoot)
	if err != nil {
		t.Fatal(err)
	}
	balance := stateDB.GetBalance(testBank)
	t.Log(balance)
}

func newBlockchainWithExistsDB(n int, deployContract bool, db *database.MemDatabase) syncer.BlockChain {
	remoteDB := database.NewIpfsDbWithAdapter(database.NewFakeIpfsAdapter())
	gspec := core.DefaultGenesisBlock()
	gspec.Alloc = core.GenesisAlloc{testBank: {Balance: testBankBalance}}
	genesis := gspec.MustCommit(db)
	config := gspec.Config
	dporConfig := config.Dpor
	dporFakeEngine := dpor.NewFaker(dporConfig, db)

	// Define three accounts to simulate transactions with
	acc1Key, _ := crypto.HexToECDSA("8a1f9a8f95be41cd7ccb6168179afb4504aefe388d1e14474d32c45c72ce7b7a")
	acc2Key, _ := crypto.HexToECDSA("49a7b37aa6f6645917e7b807e9d1c00d4fa71f18343b0d4122a4d2df64dd6fee")
	acc1Addr := crypto.PubkeyToAddress(acc1Key.PublicKey)
	acc2Addr := crypto.PubkeyToAddress(acc2Key.PublicKey)

	signer := types.HomesteadSigner{}
	// Create a chain generator with some simple transactions (blatantly stolen from @fjl/chain_markets_test)
	generator := func(i int, block *core.BlockGen) {
		switch i {
		case 0:
			// In block 1, the test bank sends account #1 some ether.
			tx, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank), acc1Addr, big.NewInt(10000), configs.TxGas, nil, nil), signer, testBankKey)
			block.AddTx(tx)
		case 1:
			// In block 2, the test bank sends some more ether to account #1.
			// acc1Addr passes it on to account #2.
			tx1, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank), acc1Addr, big.NewInt(20000000), configs.TxGas, nil, nil), signer, testBankKey)
			tx2, _ := types.SignTx(types.NewTransaction(block.TxNonce(acc1Addr), acc2Addr, big.NewInt(2000), configs.TxGas, nil, nil), signer, acc1Key)
			block.AddTx(tx1)
			block.AddTx(tx2)
		case 2:
			// In block 2, the test bank sends some more ether to account #1.
			// acc1Addr passes it on to account #2.
			tx1, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank), acc1Addr, big.NewInt(1000), configs.TxGas, nil, nil), signer, testBankKey)
			tx2, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank)+uint64(1), acc2Addr, big.NewInt(10000), configs.TxGas, nil, nil), signer, testBankKey)
			block.AddTx(tx1)
			block.AddTx(tx2)
		case 3:
			// Block 3 is empty but was mined by account #2.
			block.SetCoinbase(acc2Addr)
		case 4:
			// In block 1, the test bank sends account #1 some ether.
			tx, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank), acc1Addr, big.NewInt(100), configs.TxGas, nil, nil), signer, testBankKey)
			block.AddTx(tx)
		}
	}
	blocks, _ := core.GenerateChain(config, genesis, dporFakeEngine, db, remoteDB, n, generator)
	blockchain, _ := core.NewBlockChain(db, nil, gspec.Config, dporFakeEngine, vm.Config{}, remoteDB, nil)
	_, _ = blockchain.InsertChain(blocks)
	return blockchain
}
