package syncer_test

import (
	"fmt"
	"math"
	"math/big"
	"strconv"
	"sync/atomic"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/contracts/dpor/admission"
	"bitbucket.org/cpchain/chain/contracts/dpor/campaign"
	"bitbucket.org/cpchain/chain/contracts/proxy"
	"bitbucket.org/cpchain/chain/contracts/reward"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/protocols/cpc/syncer"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/event"
)

var (
	testBankKey, _  = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	testBank        = crypto.PubkeyToAddress(testBankKey.PublicKey)
	testBankBalance = new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))
	rewardAddr      common.Address
	campaignAddr    common.Address
	acAddr          common.Address
)

func newSyncer(chain syncer.BlockChain) syncer.Syncer {
	return syncer.New(chain, nil, new(event.TypeMux))
}

func TestSyncerNormal(t *testing.T) {
	var (
		n            = 1000
		badIdx       = 0
		p            = NewFakePeer(n, badIdx, false)
		head, height = p.Head()
	)

	_ = p

	// new a local chain, only genesis block in it
	localchain := newBlockchain(0, false)

	// create a syncer to sync blocks
	localSyncer := newSyncer(localchain)

	// go sync
	go localSyncer.Synchronise(p, head, height, syncer.FullSync)
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

func TestSyncerErrOrder(t *testing.T) {
	var (
		n            = 1000
		badIdx       = 0
		p            = NewFakePeer(n, badIdx, false)
		head, height = p.Head()
	)

	_ = p

	syncer.MaxQueueSize = 1

	// new a local chain, only genesis block in it
	localchain := newBlockchain(0, false)

	// create a syncer to sync blocks
	localSyncer := newSyncer(localchain)

	syncer.MaxQueueSize = 100

	// go sync
	quitCh := make(chan struct{})
	go func() {
		err := localSyncer.Synchronise(p, head, height, syncer.FullSync)
		if err == syncer.ErrQueueFull {
			t.Log("the queue is full")
		}
		quitCh <- struct{}{}
	}()
	defer localSyncer.Terminate()

	// go fake peer request handle loop
	go p.returnBlocksLoop()
	defer p.quit()

	// act as handleSyncMsg in protocol manager
	for {
		select {

		// received blocks from remote peer, deliever to syncer
		case blocks := <-p.returnCh:
			localSyncer.DeliverBlocks(p.IDString(), blocks)
		case <-quitCh:
			// if all blocks synced, return
			return
		}
	}
}

func TestSyncerTimeout(t *testing.T) {
	t.SkipNow()
	var (
		n            = 1000
		badIdx       = 0
		p            = NewFakePeer(n, badIdx, false)
		head, height = p.Head()
	)

	_ = p

	// new a local chain, only genesis block in it
	localchain := newBlockchain(0, false)

	// create a syncer to sync blocks
	localSyncer := newSyncer(localchain)

	// go sync
	err := localSyncer.Synchronise(p, head, height, syncer.FullSync)

	t.Log("err", err)

	if err != syncer.ErrTimeout {
		t.Fail()
	}

}

func TestSyncerInvalidChain(t *testing.T) {
	var (
		n            = 1000
		badIdx       = 10
		p            = NewFakePeer(n, badIdx, false)
		head, height = p.Head()
	)

	_ = p

	// new a local chain, only genesis block in it
	localchain := newBlockchain(0, false)

	// create a syncer to sync blocks
	localSyncer := newSyncer(localchain)

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
	err := localSyncer.Synchronise(p, head, height, syncer.FullSync)
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
		p            = NewFakePeer(n, badIdx, false)
		head, height = p.Head()
	)

	_ = p

	// new a local chain, only genesis block in it
	localchain := newBlockchain(0, false)

	// create a syncer to sync blocks
	localSyncer := newSyncer(localchain)

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
	err := localSyncer.Synchronise(p, head, height, syncer.FullSync)
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
		p            = NewFakePeer(n, badIdx, false)
		head, height = p.Head()
	)

	_ = p

	// new a local chain, only genesis block in it
	localchain := newBlockchain(200, false)

	// create a syncer to sync blocks
	localSyncer := newSyncer(localchain)

	// go sync
	err := localSyncer.Synchronise(p, head, height, syncer.FullSync)
	defer localSyncer.Terminate()

	t.Log(err)
	if err != syncer.ErrSlowPeer {
		t.Fail()
	}
}

func TestValidateReceiptsByManyPeers(t *testing.T) {
	syncer.MinFullBlocks = 32
	// validateReceiptsByManyPeers(t, 100, 1, false)
	// validateReceiptsByManyPeers(t, 100, 3, false)
	validateReceiptsByManyPeers(t, 200, 3, false)
	// validateReceiptsByManyPeers(t, 1000, 3, false)
	syncer.MinFullBlocks = 1024
}

func TestErrorValidateReceiptsByManyPeers(t *testing.T) {
	syncer.MinFullBlocks = 0
	validateReceiptsByManyPeers(t, 20, 20, true)
	syncer.MinFullBlocks = 1024
}

func validateReceiptsByManyPeers(t *testing.T, numbers int, peerCnt int, registerErr bool) {
	t.Log("registerErr", registerErr)
	var (
		peers = NewManyFakePeer(peerCnt, numbers, true)
	)

	localchain, db := newBlockchainWithDB(0, false)
	localchain.SetSyncMode(syncer.FastSync)

	t.Log(localchain.CurrentBlock().NumberU64())
	t.Log(localchain.CurrentFastBlock().NumberU64())

	// localchain, db := newBlockchainWithDB(0, false)
	t.Log("Peers Cnt:", len(peers), "init db keys", len(db.Keys()))

	t.Log("Genesis Hash", localchain.CurrentFastBlock().Hash().Hex())

	removePeerCh := make(chan string, 1)
	quitCh := make(chan bool, 1)

	// create a syncer to sync blocks
	localSyncer := syncer.New(localchain, func(peer string) {
		removePeerCh <- peer
	}, new(event.TypeMux))

	// add peers
	for _, peer := range peers {
		localSyncer.AddPeer(peer)
	}

	// sync with peer1
	p := peers[0]
	head, height := p.Head()
	t.Log("p latest state root:", p.blockchain.CurrentBlock().StateRoot().Hex())

	// error
	if registerErr {
		p.errorPeer = true
	}

	errCh := make(chan error, 1)

	// go sync
	go func() {
		err := localSyncer.Synchronise(p, head, height, syncer.FastSync)
		if err != nil {
			errCh <- err
		} else {
			quitCh <- true
			log.Info("Finish")
		}
	}()
	defer localSyncer.Terminate()

	for _, peer := range peers {
		// go fake peer request handle loop
		go peer.returnBlocksLoop()
		defer peer.quit()
		go func(peer *FakePeer) {
			for {
				select {
				// received blocks from remote peer, deliever to syncer
				case blocks := <-peer.returnCh:
					localSyncer.DeliverBlocks(peer.IDString(), blocks)
				// received receipts from remote peer deliver to syncer
				case receipts := <-peer.returnReceiptsCh:
					// return only 10 receipts in first batch
					// if localchain.CurrentFastBlock().NumberU64() < 1 {
					// 	localSyncer.DeliverReceipts(peer.IDString(), receipts[0:10])
					// } else {
					// 	localSyncer.DeliverReceipts(peer.IDString(), receipts)
					// }
					localSyncer.DeliverReceipts(peer.IDString(), receipts)
				case data := <-peer.returnStateDataCh:
					if len(data) == 4 {
						data = data[:2]
					}
					localSyncer.DeliverNodeData(peer.IDString(), data)
				case headers := <-peer.returnHeadersCh:
					localSyncer.DeliverHeaders(peer.IDString(), headers)
				case bodies := <-peer.returnBodiesCh:
					localSyncer.DeliverBodies(peer.IDString(), bodies)
				}
			}
		}(peer)
	}

	for {
		select {
		case err := <-errCh:
			if registerErr && err == syncer.ErrReceiptValidate {
				t.Log(err.Error())
			} else {
				t.Error(err)
			}
			return
		case peer := <-removePeerCh:
			localSyncer.RemovePeer(peer)
		case <-quitCh:
			log.Info("blocks and receipts sync successful")

			t.Log("sync successfully!")

			b1 := localchain.GetBlockByNumber(1)
			b1Txs := len(b1.Transactions())
			t.Log("Transactions cnt of block1:", b1Txs)

			t.Log("number", localchain.CurrentFastBlock().Number(), "db keys cnt", len(db.Keys()), len(p.db.Keys()))
			state, err := localchain.State()
			if err != nil {
				t.Fatal(err)
			}
			balance := state.GetBalance(testBank)
			t.Log("Bank balance:", balance, state.Empty(testBank))
			if balance.Uint64() >= testBankBalance.Uint64() {
				t.Error("Bank balance error, account state is error.")
			}
			// code check
			stateP, _ := p.blockchain.State()
			rewardP := stateP.GetCode(rewardAddr)
			reward := state.GetCode(rewardAddr)
			t.Log("reward contract data length:", len(reward))
			if len(rewardP) != len(reward) {
				t.Error("check reward code error:", len(rewardP), len(reward))
			}
			t.Log(localchain.CurrentBlock().NumberU64())
			return
		}
	}
}

func TestOnlyFullSync(t *testing.T) {
	syncer.MinFullBlocks = 32
	validateReceiptsByManyPeers(t, 20, 3, false)
	syncer.MinFullBlocks = 1024
}

func TestCallSyncTwice(t *testing.T) {
	t.Skip("skip now")
	var (
		n            = 1000
		badIdx       = 0
		p            = NewFakePeer(n, badIdx, false)
		head, height = p.Head()
	)

	_ = p

	syncer.MinFullBlocks = 32

	// new a local chain, only genesis block in it
	localchain := newBlockchain(0, false)

	// create a syncer to sync blocks
	localSyncer := newSyncer(localchain)

	var (
		offline        int32
		headerFetchCnt int32
		afterOffline   int32
	)
	atomic.StoreInt32(&offline, 0)
	atomic.StoreInt32(&headerFetchCnt, 0)
	atomic.StoreInt32(&afterOffline, 0)

	// go sync
	quitCh := make(chan struct{})
	go func() {
		err := localSyncer.Synchronise(p, head, height, syncer.FastSync)
		if err != nil {
			if err != syncer.ErrTimeout {
				t.Error(err)
				quitCh <- struct{}{}
			} else {
				atomic.StoreInt32(&headerFetchCnt, 0)
				atomic.StoreInt32(&offline, 0)
				atomic.StoreInt32(&afterOffline, 1)
				err := localSyncer.Synchronise(p, head, height, syncer.FastSync)
				if err != nil {
					t.Error(err)
				}
				quitCh <- struct{}{}
			}
		} else {
			quitCh <- struct{}{}
		}
	}()
	defer localSyncer.Terminate()

	// go fake peer request handle loop
	go p.returnBlocksLoop()
	defer p.quit()

	go func(peer *FakePeer) {
		for {
			select {
			case blocks := <-peer.returnCh:
				localSyncer.DeliverBlocks(peer.IDString(), blocks)
			// received receipts from remote peer deliver to syncer
			case receipts := <-peer.returnReceiptsCh:
				if atomic.LoadInt32(&offline) == 1 {
					continue
				}
				localSyncer.DeliverReceipts(peer.IDString(), receipts)
			case data := <-peer.returnStateDataCh:
				if atomic.LoadInt32(&offline) == 1 {
					continue
				}
				localSyncer.DeliverNodeData(peer.IDString(), data)
			case headers := <-peer.returnHeadersCh:
				log.Info("fetch headers", "number", headers[0].Number.Uint64(), "offline", atomic.LoadInt32(&offline))
				if atomic.LoadInt32(&offline) == 1 {
					continue
				}
				atomic.StoreInt32(&headerFetchCnt, atomic.LoadInt32(&headerFetchCnt)+1)
				localSyncer.DeliverHeaders(peer.IDString(), headers)
				if atomic.LoadInt32(&afterOffline) == 0 && headers[0].Number.Uint64() >= uint64(400) && atomic.LoadInt32(&headerFetchCnt) > 1 {
					atomic.StoreInt32(&offline, 1)
				}
			case bodies := <-peer.returnBodiesCh:
				if atomic.LoadInt32(&offline) == 1 {
					continue
				}
				localSyncer.DeliverBodies(peer.IDString(), bodies)
			}
		}
	}(p)

	// act as handleSyncMsg in protocol manager
	for {
		select {
		case <-quitCh:
			// if all blocks synced, return
			syncer.MinFullBlocks = 1024
			return
		}
	}
}

func TestGetBalanceAtMiddleBlock(t *testing.T) {
	var (
		peerCnt = 1
		numbers = 200
		peers   = NewManyFakePeer(peerCnt, numbers, true)
	)

	localchain, db := newBlockchainWithDB(0, false)
	localchain.SetSyncMode(syncer.FastSync)

	removePeerCh := make(chan string, 1)
	quitCh := make(chan bool, 1)

	// create a syncer to sync blocks
	localSyncer := syncer.New(localchain, func(peer string) {
		removePeerCh <- peer
	}, new(event.TypeMux))

	// add peers
	for _, peer := range peers {
		localSyncer.AddPeer(peer)
	}

	// sync with peer1
	p := peers[0]
	head, height := p.Head()

	errCh := make(chan error, 1)

	// go sync
	go func() {
		err := localSyncer.Synchronise(p, head, height, syncer.FullSync)
		if err != nil {
			errCh <- err
		} else {
			quitCh <- true
			log.Info("Finish")
		}
	}()
	defer localSyncer.Terminate()

	for _, peer := range peers {
		// go fake peer request handle loop
		go peer.returnBlocksLoop()
		defer peer.quit()
		go func(peer *FakePeer) {
			for {
				select {
				// received blocks from remote peer, deliever to syncer
				case blocks := <-peer.returnCh:
					localSyncer.DeliverBlocks(peer.IDString(), blocks)
				// received receipts from remote peer deliver to syncer
				case receipts := <-peer.returnReceiptsCh:
					localSyncer.DeliverReceipts(peer.IDString(), receipts)
				case data := <-peer.returnStateDataCh:
					localSyncer.DeliverNodeData(peer.IDString(), data)
				case headers := <-peer.returnHeadersCh:
					localSyncer.DeliverHeaders(peer.IDString(), headers)
				case bodies := <-peer.returnBodiesCh:
					localSyncer.DeliverBodies(peer.IDString(), bodies)
				}
			}
		}(peer)
	}

	for {
		select {
		case err := <-errCh:
			t.Error(err)
			return
		case peer := <-removePeerCh:
			localSyncer.RemovePeer(peer)
		case <-quitCh:
			log.Info("blocks and receipts sync successful")

			t.Log("sync successfully!")

			b1 := localchain.GetBlockByNumber(1)
			b1Txs := len(b1.Transactions())
			t.Log("Transactions cnt of block1:", b1Txs)

			t.Log("number", localchain.CurrentFastBlock().Number(), "db keys cnt", len(db.Keys()), len(p.db.Keys()))
			state, err := localchain.State()
			if err != nil {
				t.Fatal(err)
			}
			balance := state.GetBalance(testBank)
			t.Log("Bank balance:", balance, state.Empty(testBank))
			if balance.Uint64() >= testBankBalance.Uint64() {
				t.Error("Bank balance error, account state is error.")
			}

			// state at middle block
			block51 := localchain.GetBlockByNumber(uint64(51))
			root51 := block51.StateRoot()
			if state51, err := localchain.StateAt(root51); err == nil {
				if state51 == nil {
					t.Fatal("state51 is nil")
				} else {
					t.Log("Bank balance at block 51:", state51.GetBalance(testBank))
				}
			} else {
				t.Fatal(err)
			}

			// code check
			stateP, _ := p.blockchain.State()
			rewardP := stateP.GetCode(rewardAddr)
			reward := state.GetCode(rewardAddr)
			t.Log("reward contract data length:", len(reward))
			if len(rewardP) != len(reward) {
				t.Error("check reward code error:", len(rewardP), len(reward))
			}
			t.Log(localchain.CurrentBlock().NumberU64())
			return
		}
	}
}

func newBlockchainWithDB(n int, deployContract bool) (syncer.BlockChain, *database.MemDatabase) {
	db := database.NewMemDatabase()
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
			tx, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank), acc1Addr, big.NewInt(100000), configs.TxGas, nil, nil), signer, testBankKey)
			block.AddTx(tx)
		case 1:
			// In block 2, the test bank sends some more ether to account #1.
			// acc1Addr passes it on to account #2.
			tx1, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank), acc1Addr, big.NewInt(1000), configs.TxGas, nil, nil), signer, testBankKey)
			tx2, _ := types.SignTx(types.NewTransaction(block.TxNonce(acc1Addr), acc2Addr, big.NewInt(1000), configs.TxGas, nil, nil), signer, acc1Key)
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
		case 50:
			tx1, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank), acc1Addr, big.NewInt(10000000), configs.TxGas, nil, nil), signer, testBankKey)
			tx2, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank)+uint64(1), acc2Addr, big.NewInt(10000), configs.TxGas, nil, nil), signer, testBankKey)
			block.AddTx(tx1)
			block.AddTx(tx2)
		case 130:
			tx1, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank), acc1Addr, big.NewInt(10000000), configs.TxGas, nil, nil), signer, testBankKey)
			tx2, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank)+uint64(1), acc2Addr, big.NewInt(10000), configs.TxGas, nil, nil), signer, testBankKey)
			block.AddTx(tx1)
			block.AddTx(tx2)
		}
	}
	blocks, _ := core.GenerateChain(config, genesis, dporFakeEngine, db, remoteDB, n, generator)
	blockchain, _ := core.NewBlockChain(db, nil, gspec.Config, dporFakeEngine, vm.Config{}, remoteDB, nil)
	_, _ = blockchain.InsertChain(blocks)

	// deploy contract
	if deployContract {
		backend := backends.NewDporSimulatedBackendWithExistsBlockchain(db, blockchain, config)

		var err error
		deployTransactor := bind.NewKeyedTransactor(testBankKey)

		_, _, _, err = proxy.DeployProxyContractRegister(deployTransactor, backend)
		rewardAddr, _, _, err = reward.DeployReward(deployTransactor, backend)
		acAddr, _, _, err = admission.DeployAdmission(deployTransactor, backend, big.NewInt(5), big.NewInt(5), big.NewInt(10), big.NewInt(10))
		campaignAddr, _, _, err = campaign.DeployCampaign(deployTransactor, backend, acAddr, rewardAddr)
		if err != nil {
			log.Fatal(err.Error())
		}
		backend.Commit()

		// Call Campaign Contract
		fakeClaimCampaign(backend)
	}
	return blockchain, db
}

func fakeClaimCampaign(backend *backends.SimulatedBackend) {
	// transactOpts := bind.NewKeyedTransactor(testBankKey)

	// campaignInstance, _ := campaign.NewCampaign(campaignAddr, backend)
	// // ClaimCampaign 1st time
	// cpuNonce := uint64(100)
	// cpuBlockNum := int64(200)
	// memNonce := uint64(100)
	// memBlockNum := int64(200)
	// _, err := campaignInstance.ClaimCampaign(transactOpts, big.NewInt(1), cpuNonce, big.NewInt(cpuBlockNum), memNonce, big.NewInt(memBlockNum), big.NewInt(configs.CampaignVersion))

	// if err != nil {
	// 	log.Fatal("campaign error", "err", err)
	// }
	// backend.Commit()
}

func newBlockchain(n int, deployContract bool) syncer.BlockChain {
	blockchain, _ := newBlockchainWithDB(n, deployContract)
	return blockchain
}

type FakePeer struct {
	badBlockIdx       int
	blockchain        syncer.BlockChain
	db                *database.MemDatabase
	requestCh         chan uint64
	returnCh          chan types.Blocks
	returnReceiptsCh  chan []types.Receipts
	returnStateDataCh chan [][]byte
	returnHeadersCh   chan []*types.Header
	returnBodiesCh    chan [][]*types.Transaction
	quitCh            chan struct{}
	id                int
	errorPeer         bool
}

func NewManyFakePeer(n int, blockNumbers int, deployContract bool) []*FakePeer {
	peers := make([]*FakePeer, n)
	for i := 0; i < n; i++ {
		peers[i] = NewFakePeer(blockNumbers, 0, deployContract)
		peers[i].id = i
	}
	return peers
}

func NewFakePeer(n int, badIdx int, deployContract bool) *FakePeer {
	blockchain, db := newBlockchainWithDB(n, deployContract)
	return &FakePeer{
		badBlockIdx:       badIdx,
		blockchain:        blockchain,
		db:                db,
		requestCh:         make(chan uint64),
		returnCh:          make(chan types.Blocks),
		returnReceiptsCh:  make(chan []types.Receipts),
		returnStateDataCh: make(chan [][]byte),
		returnHeadersCh:   make(chan []*types.Header),
		returnBodiesCh:    make(chan [][]*types.Transaction),
		quitCh:            make(chan struct{}),
		id:                0,
	}
}

func (fp *FakePeer) IDString() string {
	return "fake peer " + strconv.Itoa(fp.id)
}

func (fp *FakePeer) Head() (hash common.Hash, ht *big.Int) {
	return fp.blockchain.CurrentBlock().Hash(), fp.blockchain.CurrentBlock().Number()
}

func (fp *FakePeer) SendGetBlocks(start uint64) error {
	fp.requestCh <- start
	return nil
}

func (fp *FakePeer) RequestReceipts(hashes []common.Hash) error {
	receipts := []types.Receipts{}
	for _, hash := range hashes {
		receipts = append(receipts, fp.blockchain.GetReceiptsByHash(hash))
	}

	if fp.errorPeer {
		receipts[0], receipts[1] = receipts[1], receipts[0]
	}
	fp.returnReceiptsCh <- receipts
	return nil
}

func (fp *FakePeer) RequestNodeData(hashes []common.Hash) error {
	var data [][]byte
	for _, hash := range hashes {
		if entry, err := fp.blockchain.TrieNode(hash); err == nil {
			data = append(data, entry)
		} else {
			log.Error(err.Error())
		}
	}
	fp.returnStateDataCh <- data
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

func (fp *FakePeer) RequestHeadersByNumber(origin uint64, amount int, skip int, reverse bool) error {
	var headers []*types.Header
	for len(headers) < int(amount) {
		header := fp.blockchain.GetHeaderByNumber(origin)
		if header == nil {
			fp.returnHeadersCh <- headers
			return nil
		}
		headers = append(headers, header)
		origin++
	}
	fp.returnHeadersCh <- headers
	return nil
}

func (fp *FakePeer) RequestBodies(hashes []common.Hash) error {
	var transactions [][]*types.Transaction
	for _, hash := range hashes {
		transactions = append(transactions, fp.blockchain.GetBlockByHash(hash).Transactions())
	}
	fp.returnBodiesCh <- transactions
	return nil
}
