// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package rpt_test

import (
	"context"
	"fmt"
	"math/big"
	"math/rand"
	"strconv"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	cr "bitbucket.org/cpchain/chain/contracts/dpor/rpt"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

// --- --- --- --- --- --- --- --- --- --- --- below are bench tests for new rpt calculation method --- --- --- --- --- --- --- --- --- --- ---

var (
	testBankKey, _  = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	testBank        = crypto.PubkeyToAddress(testBankKey.PublicKey)
	testBankBalance = new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))
	rptAddr         common.Address
)

func newBlockchain(n int) *core.BlockChain {
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

func newBlockchainWithBalances(n int, accounts []common.Address) *core.BlockChain {
	db := database.NewMemDatabase()
	remoteDB := database.NewIpfsDbWithAdapter(database.NewFakeIpfsAdapter())
	gspec := core.DefaultGenesisBlock()

	for i, addr := range accounts {
		gspec.Alloc[addr] = core.GenesisAccount{Balance: new(big.Int).Mul(big.NewInt(int64(i/3)), big.NewInt(configs.Cpc))}

		log.Info("alloc", "addr", addr.Hex(), "i", i, "bal", i/3)
	}

	genesis := gspec.MustCommit(db)
	config := gspec.Config
	dporConfig := config.Dpor
	dporFakeEngine := dpor.NewFaker(dporConfig, db)
	blocks, _ := core.GenerateChain(config, genesis, dporFakeEngine, db, remoteDB, n, nil)
	blockchain, _ := core.NewBlockChain(db, nil, gspec.Config, dporFakeEngine, vm.Config{}, remoteDB, nil)
	_, _ = blockchain.InsertChain(blocks)
	return blockchain
}

type fakeChainBackendForRptCollector struct {
	blockchain *core.BlockChain
}

func newFakeChainBackendForRptCollector(n int) *fakeChainBackendForRptCollector {
	bc := newBlockchain(n)
	return &fakeChainBackendForRptCollector{
		blockchain: bc,
	}
}

func newFakeChainBackendForRptCollectorWithBalances(n int, accounts []common.Address) *fakeChainBackendForRptCollector {
	bc := newBlockchainWithBalances(n, accounts)
	return &fakeChainBackendForRptCollector{
		blockchain: bc,
	}
}

func (fc *fakeChainBackendForRptCollector) HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error) {
	return fc.blockchain.GetBlockByNumber(number.Uint64()).Header(), nil
}

func (fc *fakeChainBackendForRptCollector) BalanceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (*big.Int, error) {
	header, err := fc.HeaderByNumber(ctx, blockNumber)
	state, err := fc.blockchain.StateAt(header.StateRoot)
	if state == nil || err != nil {
		return nil, err
	}
	return state.GetBalance(account), state.Error()
}

func (fc *fakeChainBackendForRptCollector) NonceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (uint64, error) {
	header, err := fc.HeaderByNumber(ctx, blockNumber)
	state, err := fc.blockchain.StateAt(header.StateRoot)
	if state == nil || err != nil {
		return 0, err
	}
	return state.GetNonce(account), state.Error()
}

func generateABatchAccounts(n int) []common.Address {
	var addresses []common.Address
	for i := 1; i < n; i++ {
		addresses = append(addresses, common.HexToAddress("0x"+fmt.Sprintf("%040x", i)))
	}
	return addresses
}

func BenchmarkRptOf_10a(b *testing.B) {
	benchRptOf(b, 10)
}

func BenchmarkRptOf_100a(b *testing.B) {
	benchRptOf(b, 100)
}

func BenchmarkRptOf_200a(b *testing.B) {
	benchRptOf(b, 200)
}

func BenchmarkRptOf_1000a(b *testing.B) {
	benchRptOf(b, 1000)
}

func benchRptOf(b *testing.B, numAccount int) {
	b.ReportAllocs()
	b.ResetTimer()

	addrs := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollector(1000)

	rptCollector := rpt.NewRptCollectorImpl6(nil, fc)
	for i, addr := range addrs {
		rpt := rptCollector.RptOf(addr, addrs, 500)
		b.Log("idx", i, "rpt", rpt.Rpt, "addr", addr.Hex())
	}
}

//Benchmark of rpt...
// this testcase construct 1000 blocks

func BenchmarkCalcRptInfoList_100n(b *testing.B) {
	benchCalcRptInfoList(b, 100)
}

// 100 candidates' rpt with window size 100 spend 0.09 ns every time

func BenchmarkCalcRptInfoList_1000n(b *testing.B) {
	benchCalcRptInfoList(b, 1000)
}

// 1000 candidates' rpt with window size 1000 spend 1424020047 ns every time

func benchCalcRptInfoList(b *testing.B, num int) {
	b.ReportAllocs()
	b.ResetTimer()

	numAccount := num
	accounts := generateABatchAccounts(numAccount)
	contractAddr, backend := newBlockchainWithDb(1000)
	rptInstance, _ := rpt.NewRptService(contractAddr, backend)
	rpts := rptInstance.CalcRptInfoList(accounts, transfer(100))
	b.Log("rpt result", "rpts", rpts)
}

//benchmark of rpt_calc:
//benchmark of balance:
func benchBalanceValueOf(b *testing.B, blocknum int) {
	b.ReportAllocs()
	b.ResetTimer()

	numAccount := 30
	numBlocks := blocknum
	windowNum := rand.Intn(10000)
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl6(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.BalanceValueOf(addr, accounts, 500, windowNum)
		b.Log("idx", i, "Balance Value of reputation", rank, "addr", addr.Hex())
	}
}

func BenchmarkBalanceValueOf_1000b(b *testing.B) {
	benchBalanceValueOf(b, 1000)
}

func BenchmarkBalanceValueOf_5000b(b *testing.B) {
	benchBalanceValueOf(b, 5000)
}

func BenchmarkBalanceValueOf_10000b(b *testing.B) {
	benchBalanceValueOf(b, 10000)
}

//benchmark of Txs:
func benchTxsValueOf(b *testing.B, blocknum int) {
	b.ReportAllocs()
	b.ResetTimer()

	numAccount := 30
	numBlocks := blocknum
	windowNum := rand.Intn(10000)
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl6(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.TxsValueOf(addr, accounts, 500, windowNum)
		b.Log("idx", i, "Txs Value of reputation", rank, "addr", addr.Hex())
	}
}

func BenchmarkTxsValueOf_1000b(b *testing.B) {
	benchTxsValueOf(b, 1000)
}

func BenchmarkTxsValueOf_10000b(b *testing.B) {
	benchTxsValueOf(b, 10000)
}

//benchmark of Maintenance:
func benchMaintenanceValueOf(b *testing.B, blocknum int) {
	b.ReportAllocs()
	b.ResetTimer()

	numAccount := 30
	numBlocks := blocknum
	windowNum := rand.Intn(10000)
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl6(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.MaintenanceValueOf(addr, accounts, 500, windowNum)
		b.Log("idx", i, "Maintenance Value of reputation", rank, "addr", addr.Hex())
	}
}

func BenchmarkMaintenanceValueOf_1000b(b *testing.B) {
	benchMaintenanceValueOf(b, 1000)
}

func BenchmarkMaintenanceValueOf_10000b(b *testing.B) {
	benchMaintenanceValueOf(b, 10000)
}

//benchmark of Upload:
func benchUploadValueOf(b *testing.B, blocknum int) {
	b.ReportAllocs()
	b.ResetTimer()

	numAccount := 30
	numBlocks := blocknum
	windowNum := rand.Intn(10000)
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl6(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.UploadValueOf(addr, accounts, 500, windowNum)
		b.Log("idx", i, "Upload Value of reputation", rank, "addr", addr.Hex())
	}
}

func BenchmarkUploadValueOf_1000b(b *testing.B) {
	benchUploadValueOf(b, 1000)
}

func BenchmarkUploadValueOf_10000b(b *testing.B) {
	benchUploadValueOf(b, 10000)
}

////benchmark of Proxy:
func benchProxyValueOf(b *testing.B, blocknum int) {
	b.ReportAllocs()
	b.ResetTimer()

	numAccount := 30
	numBlocks := blocknum
	windowNum := rand.Intn(10000)
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl6(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.ProxyValueOf(addr, accounts, 500, windowNum)
		b.Log("idx", i, "Proxy Value of reputation", rank, "addr", addr.Hex())
	}
}

func BenchmarkProxyValueOf_1000b(b *testing.B) {
	benchProxyValueOf(b, 1000)
}

func BenchmarkProxyValueOf_10000b(b *testing.B) {
	benchProxyValueOf(b, 10000)
}

//benchmark of rpt_helper:
func benchLowRptCount(b *testing.B, total int) {
	b.ReportAllocs()
	b.ResetTimer()

	contractAddr, backend := newBlockchainWithDb(1000)
	rptInstance, _ := rpt.NewRptService(contractAddr, backend)
	lowCount := rptInstance.LowRptCount(total)
	b.Log("LowRptCount is", lowCount)
}

func BenchmarkLowRptCount_1000t(b *testing.B) {
	benchLowRptCount(b, 1000)
}

func BenchmarkLowRptCount_10000t(b *testing.B) {
	benchLowRptCount(b, 10000)
}

//Additional functions
func transfer(num int) uint64 {
	str := strconv.Itoa(num)
	number, _ := strconv.ParseUint(str, 12, 64)
	return number
}

// Construct a new Contract address and a backend instance
func newBlockchainWithDb(n int) (common.Address, *backends.SimulatedBackend) {
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

	backend := backends.NewDporSimulatedBackendWithExistsBlockchain(db, blockchain, config)

	var err error
	deployTransactor := bind.NewKeyedTransactor(testBankKey)

	rptAddr, _, _, err = cr.DeployRpt(deployTransactor, backend)
	if err != nil {
		log.Fatal(err.Error())
	}
	backend.Commit()

	return rptAddr, backend
}
