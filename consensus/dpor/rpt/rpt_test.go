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
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	cr "bitbucket.org/cpchain/chain/contracts/dpor/rpt"
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
	testBankBalance = new(big.Int).Mul(big.NewInt(10000), big.NewInt(configs.Cpc))
	rptAddr         common.Address
)

// create a simulated blockchain with n blocks
func newBlockchain(n int) *core.BlockChain {
	db := database.NewMemDatabase()
	remoteDB := database.NewIpfsDbWithAdapter(database.NewFakeIpfsAdapter())
	gspec := core.DefaultGenesisBlock()
	genesis := gspec.MustCommit(db)
	config := gspec.Config
	dporConfig := config.Dpor
	// fake a dpor engine
	dporFakeEngine := dpor.NewFaker(dporConfig, db)
	// generate blocks
	blocks, _ := core.GenerateChain(config, genesis, dporFakeEngine, db, remoteDB, n, nil)
	blockchain, _ := core.NewBlockChain(db, nil, gspec.Config, dporFakeEngine, vm.Config{}, remoteDB, nil)
	_, _ = blockchain.InsertChain(blocks)
	return blockchain
}

// create blockchain with n blocks and some accounts
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

// benchs of default parameters
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

	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
	for i, addr := range addrs {
		rpt := rptCollector.RptOf(addr, addrs, 500)
		b.Log("idx", i, "rpt", rpt.Rpt, "addr", addr.Hex())
	}
}

//Benchmark of rpt...
//This testcase construct 1000 blocks

// 1. The relationships between performance and the number of candidate
// On the precondition of default windowSize (100)
// 10 candidates' rpt with window size 100 spend about 0.003s every time
func BenchmarkCalcRptInfoList_10c(b *testing.B) {
	benchCalcRptInfoList(b, 100, 10)
}

// 50 candidates' rpt with window size 100 spend about 0.015s every time
func BenchmarkCalcRptInfoList_50c(b *testing.B) {
	benchCalcRptInfoList(b, 100, 50)
}

// 100 candidates' rpt with window size 100 spend about 0.038s every time
func BenchmarkCalcRptInfoList_100c(b *testing.B) {
	benchCalcRptInfoList(b, 100, 100)
}

// 500 candidates' rpt with window size 100 spend about 0.5s every time
func BenchmarkCalcRptInfoList_500c(b *testing.B) {
	benchCalcRptInfoList(b, 100, 500)
}

// 1000 candidates' rpt with window size 100 spend about 1.85s every time
func BenchmarkCalcRptInfoList_1000c(b *testing.B) {
	benchCalcRptInfoList(b, 100, 1000)
}

// 2.The relationships between performance and the size of window
// On the precondition of 100 candidates
// 100 candidates' rpt with window size 10 spend about 0.022s every time
func BenchmarkCalcRptInfoList_10w(b *testing.B) {
	benchCalcRptInfoList(b, 10, 100)
}

// 100 candidates' rpt with window size 50 spend about 0.030s every time
func BenchmarkCalcRptInfoList_50w(b *testing.B) {
	benchCalcRptInfoList(b, 50, 100)
}

// 100 candidates' rpt with window size 100 spend about 0.038s every time
func BenchmarkCalcRptInfoList_100w(b *testing.B) {
	benchCalcRptInfoList(b, 100, 100)
}

// 100 candidates' rpt with window size 500 spend about 0.039s every time
func BenchmarkCalcRptInfoList_500w(b *testing.B) {
	benchCalcRptInfoList(b, 500, 100)
}

// 100 candidates' rpt with window size 500 spend about 0.040s every time
func BenchmarkCalcRptInfoList_1000w(b *testing.B) {
	benchCalcRptInfoList(b, 1000, 100)
}

func benchCalcRptInfoList(b *testing.B, windowSize int64, numAccount int) {
	b.ReportAllocs()
	b.ResetTimer()

	accounts := generateABatchAccounts(numAccount)
	contractAddr, backend, rptContract := newBlockchainWithDb(1000, accounts)
	rptContract.UpdateWindow(bind.NewKeyedTransactor(testBankKey), big.NewInt(windowSize))
	backend.Commit()
	rptInstance, _ := rpt.NewRptService(contractAddr, backend)
	tstart := time.Now()
	rpts := rptInstance.CalcRptInfoList(accounts, uint64(1000))
	b.Log("100 candidates' rpt with window size 100 spend time", time.Now().Sub(tstart))
	b.Log("rpt result", "rpts", rpts.FormatString())
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
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
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
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
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
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
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
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
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
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
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

	numAccount := 100
	accounts := generateABatchAccounts(numAccount)
	contractAddr, backend, _ := newBlockchainWithDb(1000, accounts)
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

// Additional functions
// Construct a new Contract address and a backend instance
func newBlockchainWithDb(n int, addrs []common.Address) (common.Address, *backends.SimulatedBackend, *cr.Rpt) {
	db := database.NewMemDatabase()
	remoteDB := database.NewIpfsDbWithAdapter(database.NewFakeIpfsAdapter())
	gspec := core.DefaultGenesisBlock()
	gspec.GasLimit = 1000000
	gspec.Alloc = core.GenesisAlloc{testBank: {Balance: testBankBalance}}
	genesis := gspec.MustCommit(db)
	config := gspec.Config
	dporConfig := config.Dpor
	dporFakeEngine := dpor.NewFaker(dporConfig, db)
	from := 0
	generator := func(i int, gen *core.BlockGen) {
		number := rand.Intn(10)
		a := int64(number)
		tx := types.NewTransaction(
			gen.TxNonce(testBank),
			addrs[from],
			new(big.Int).Mul(big.NewInt(a), big.NewInt(configs.Cpc)),
			configs.TxGas,
			nil,
			nil,
		)
		tx, _ = types.SignTx(tx, types.HomesteadSigner{}, testBankKey)
		gen.AddTx(tx)

		from = (from + 1) % len(addrs)

	}

	blocks, _ := core.GenerateChain(config, genesis, dporFakeEngine, db, remoteDB, n, generator)
	blockchain, _ := core.NewBlockChain(db, nil, gspec.Config, dporFakeEngine, vm.Config{}, remoteDB, nil)
	_, _ = blockchain.InsertChain(blocks)

	backend := backends.NewDporSimulatedBackendWithExistsBlockchain(db, blockchain, config)

	var err error
	deployTransactor := bind.NewKeyedTransactor(testBankKey)

	rptAddr, _, rptContract, err := cr.DeployRpt(deployTransactor, backend)
	if err != nil {
		log.Fatal(err.Error())
	}
	backend.Commit()

	return rptAddr, backend, rptContract
}

//unit testcase:
//Testcase of rpt_calc:
func TestRptOf4(t *testing.T) {
	numAccount := 30
	numBlocks := 10000
	windowNum := rand.Intn(10000)
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.BalanceValueOf(addr, accounts, 500, windowNum)
		t.Log("idx", i, "Balance Value of reputation", rank, "addr", addr.Hex())
	}
}
func TestPrint(t *testing.T) {
	numBlocks := 1000
	windowNum := rand.Intn(10)
	accounts := generateABatchAccounts(10)

	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.BalanceValueOf(addr, accounts, 500, windowNum)
		t.Log("idx", i, "Balance Value of reputation", rank, "addr", addr.Hex())
	}
	newAddr := common.HexToAddress("8a1f9a8f95be41cd7ccb6168179afb4504aefe388d1e14474d32c45c72ce7b7a")
	rank := rptCollector.BalanceValueOf(newAddr, accounts, 500, windowNum)
	t.Log("This didn't match address :", "Balance Value of reputation", rank, "addr", newAddr.Hex())
}

func TestBalanceValueOf(t *testing.T) {
	numAccount := 5
	numBlocks := 100
	windowNum := rand.Intn(100)
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.BalanceValueOf(addr, accounts, 50, windowNum)
		t.Log("idx", i, "Balance Value of reputation", rank, "addr", addr.Hex())
	}
}

func TestTxsValueOf(t *testing.T) {
	numAccount := 5
	numBlocks := 100
	windowNum := rand.Intn(100)
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.TxsValueOf(addr, accounts, 50, windowNum)
		t.Log("idx", i, "Transaction Count of reputation", rank, "addr", addr.Hex())
	}
}

func TestMaintenanceValueOf(t *testing.T) {
	numAccount := 5
	numBlocks := 100
	windowNum := rand.Intn(100)
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.MaintenanceValueOf(addr, accounts, 50, windowNum)
		t.Log("idx", i, "Chain Maintenance of reputation", rank, "addr", addr.Hex())
	}
}

func TestUploadValueOf(t *testing.T) {
	numAccount := 5
	numBlocks := 10
	windowNum := rand.Intn(10)
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.UploadValueOf(addr, accounts, 5, windowNum)
		t.Log("idx", i, "File Contribution of reputation", rank, "addr", addr.Hex())
	}
}

func TestProxyValueOf(t *testing.T) {
	numAccount := 5
	numBlocks := 10
	windowNum := rand.Intn(10)
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.ProxyValueOf(addr, accounts, 5, windowNum)
		t.Log("idx", i, "Proxy Information of PDash of reputation", rank, "addr", addr.Hex())
	}
}

//Test the input format of every account
func TestFormatString(t *testing.T) {
	accounts := generateABatchAccounts(5)
	contractAddr, backend, _ := newBlockchainWithDb(6, accounts)
	rptInstance, _ := rpt.NewRptService(contractAddr, backend)
	rpts := rptInstance.CalcRptInfoList(accounts, 6)
	t.Log("rpt result", "rpts", rpts.FormatString())

}

func TestAddrs(t *testing.T) {
	accounts := generateABatchAccounts(5)
	contractAddr, backend, _ := newBlockchainWithDb(6, accounts)
	rptInstance, _ := rpt.NewRptService(contractAddr, backend)
	rpts := rptInstance.CalcRptInfoList(accounts, 6)
	t.Log("rpt result", "rpts", rpts.Addrs())
}

func TestSwapAndLess(t *testing.T) {
	accounts := generateABatchAccounts(6)
	contractAddr, backend, _ := newBlockchainWithDb(6, accounts)
	rptInstance, _ := rpt.NewRptService(contractAddr, backend)
	rpts := rptInstance.CalcRptInfoList(accounts, 6)
	t.Log("rpt result", "rpts'format", rpts.FormatString(), "before is less or not?", rpts.Less(0, 1))
	rpts.Swap(0, 1)
	t.Log("rpt result", "rpts'format", rpts.FormatString(), "before is less or not?", rpts.Less(0, 1))
}

//Testcase of rpt_ helper:
func TestPctCount(t *testing.T) {
	type args struct {
		pct   int
		total int
	}
	tests := []struct {
		name string
		args args
		want int
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := rpt.PctCount(tt.args.pct, tt.args.total); got != tt.want {
				t.Errorf("PctCount() = %v, want %v", got, tt.want)
			}
		})
	}
}

//testcase of rpt.go:
func TestTotalSeats(t *testing.T) {
	numAccount := 100
	accounts := generateABatchAccounts(numAccount)
	_, backend, _ := newBlockchainWithDb(1000, accounts)
	rptInstance, _ := rpt.NewRptService(common.HexToAddress("dhsjhdak"), backend)
	abLowrptseats, _ := rptInstance.LowRptSeats()
	t.Log("Abnormal situation ,not call contract:", abLowrptseats)
	contractAddr, backend, _ := newBlockchainWithDb(1000, accounts)
	rptInstance2, _ := rpt.NewRptService(contractAddr, backend)
	lowrptseats, _ := rptInstance2.LowRptSeats()
	t.Log("Normal situation, call contract:", lowrptseats)
}

func TestLowRptCount(t *testing.T) {
	numAccount := 100
	accounts := generateABatchAccounts(numAccount)
	contractAddr, backend, _ := newBlockchainWithDb(1000, accounts)
	rptInstance, _ := rpt.NewRptService(contractAddr, backend)
	lowrptsum := rptInstance.LowRptCount(77)
	t.Log("Low Rpt sum seats is:", lowrptsum)
}

func TestLowRptCount2(t *testing.T) {
	numAccount := 1000
	accounts := generateABatchAccounts(numAccount)
	contractAddr, backend, _ := newBlockchainWithDb(500, accounts)
	rptInstance, _ := rpt.NewRptService(contractAddr, backend)
	lowrptsum := rptInstance.LowRptCount(77)
	if lowrptsum != 38 {
		t.Errorf("Expected %v, but got %v", 38, lowrptsum)
	}
	t.Log("Low Rpt sum seats is:", lowrptsum)
}

func TestTxsValueWhenWindowNumIs1000(t *testing.T) {
	numAccount := 5
	numBlocks := 100
	windowNum := 1000
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)
	rptCollector := rpt.NewRptCollectorImpl(nil, fc)
	for i, addr := range accounts {
		rank := rptCollector.TxsValueOf(addr, accounts, 50, windowNum)
		t.Log("idx", i, "Transaction Count of reputation", rank, "addr", addr.Hex())
	}
}
