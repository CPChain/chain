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
	"crypto/ecdsa"
	"errors"
	"fmt"
	"math/big"
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/primitives"
	rtp_contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/rpt"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	errUnknownBlock = errors.New("unknown block")
)

var (
	key, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	addr   = crypto.PubkeyToAddress(key.PublicKey)
)

var (
	addresses = []common.Address{
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d86"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d85"),
	}
)

func newHeader() *types.Header {
	return &types.Header{
		ParentHash:   common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		Coinbase:     common.HexToAddress("0x8888f1F195AFa192CfeE860698584c030f4c9dB1"),
		StateRoot:    common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxsRoot:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptsRoot: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Number:       big.NewInt(1),
		GasLimit:     uint64(3141592),
		GasUsed:      uint64(21000),
		Time:         big.NewInt(1426516743),
		Extra:        []byte("0x0000000000000000000000000000000000000000000000000000000000000000095e7baea6a6c7c4c2dfeb977efac326af552d87e94b7b6c5a0e526a4d97f9768ad6097bde25c62ac05302acebd0730e3a18a058d7d1cb1204c4a092ef3dd127de235f15ffb4fc0d71469d1339df64650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"),
	}
}

type fakeClientBackend struct {
	rank        int64
	txVolumn    int64
	maintenance int64
	uploadCount int64
	proxyCount  int64
	isProxy     int64
}

func (b *fakeClientBackend) Rank(address common.Address, number uint64) (int64, error) {
	return b.rank, nil
}

func (b *fakeClientBackend) TxVolume(address common.Address, number uint64) (int64, error) {
	return b.txVolumn, nil
}

func (b *fakeClientBackend) Maintenance(address common.Address, number uint64) (int64, error) {
	return b.maintenance, nil
}

func (b *fakeClientBackend) UploadCount(address common.Address, number uint64) (int64, error) {
	return b.uploadCount, nil
}

func (b *fakeClientBackend) ProxyInfo(address common.Address, number uint64) (int64, int64, error) {
	return b.isProxy, b.proxyCount, nil
}

func (b *fakeClientBackend) BalanceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (*big.Int, error) {
	return big.NewInt(0), nil
}

func (b *fakeClientBackend) BlockByNumber(ctx context.Context, number *big.Int) (*types.Block, error) {
	tx1 := types.NewTransaction(0, addr, big.NewInt(10), 50000, big.NewInt(10), nil)
	tx1, _ = tx1.WithSignature(types.HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))

	var trans = make([]*types.Transaction, 1)
	trans[0] = tx1
	newBlock := types.NewBlock(newHeader(), trans, nil)
	return newBlock, nil
}

func (b *fakeClientBackend) HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error) {
	return newHeader(), nil
}

var (
	contractAddress  common.Address
	contractBackend  *backends.SimulatedBackend
	primitiveBackend *fakeClientBackend
)

func init() {
	contractBackend = backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	contractAddress, _ = deploy(key, contractBackend)
	primitiveBackend = &fakeClientBackend{}
	registerPrimitives(primitiveBackend)
}

func registerPrimitives(backend primitives.RptPrimitiveBackend) {
	vm.RegisterPrimitiveContract(common.BytesToAddress([]byte{100}), &primitives.GetRank{Backend: backend})
	vm.RegisterPrimitiveContract(common.BytesToAddress([]byte{101}), &primitives.GetMaintenance{Backend: backend})
	vm.RegisterPrimitiveContract(common.BytesToAddress([]byte{102}), &primitives.GetProxyCount{Backend: backend})
	vm.RegisterPrimitiveContract(common.BytesToAddress([]byte{103}), &primitives.GetUploadReward{Backend: backend})
	vm.RegisterPrimitiveContract(common.BytesToAddress([]byte{104}), &primitives.GetTxVolume{Backend: backend})
	vm.RegisterPrimitiveContract(common.BytesToAddress([]byte{105}), &primitives.IsProxy{Backend: backend})
}

func deploy(prvKey *ecdsa.PrivateKey, backend *backends.SimulatedBackend) (common.Address, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	addr, _, _, err := rtp_contract.DeployRpt(deployTransactor, backend)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
		return common.Address{}, err
	}
	backend.Commit()
	return addr, nil
}

type newFakeClientBackend interface {
	bind.ContractBackend

	HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error)
	BalanceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (*big.Int, error)
	NonceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (uint64, error)
}

func TestRptServiceImpl_CalcRptInfoList(t *testing.T) {
	type fields struct {
		RptContract common.Address
		Client      newFakeClientBackend
	}
	type args struct {
		addresses []common.Address
		number    uint64
	}
	tests := []struct {
		name    string
		prepare func()
		fields  fields
		args    args
		want    rpt.RptList
	}{
		{
			name:    "test for all 0 values returned by primitives",
			prepare: func() { setPrimitiveMockValues(0, 0, 0, 0, 0, 0) },
			fields: fields{
				RptContract: contractAddress,
				Client:      contractBackend,
			},
			args: args{
				addresses: addresses,
				number:    1,
			},
			want: makeExpectedRptList(addresses, 6000*2), // the blockchain has 2 blocks, each contribute 6000
		},

		{
			name:    "test for non-zero values returned by primitives",
			prepare: func() { setPrimitiveMockValues(2, 10, 1, 10, 10, 1) },
			fields: fields{
				RptContract: contractAddress,
				Client:      contractBackend,
			},
			args: args{
				addresses: addresses,
				number:    1,
			},
			want: makeExpectedRptList(addresses, 7100*2), // the blockchain has 2 blocks, each contribute 7100
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			rs, _ := rpt.NewRptService(tt.fields.Client, tt.fields.RptContract)
			tt.prepare()
			log.Printf("Testcase [%s], RPT: %v", tt.name, rs.CalcRptInfoList(tt.args.addresses, tt.args.number)[0].Rpt)
			if got := rs.CalcRptInfoList(tt.args.addresses, tt.args.number); !reflect.DeepEqual(got, tt.want) {
				t.Errorf("RptServiceImpl.CalcRptInfoList() = %+v, want %+v", got, tt.want)
			}
		})
	}
}

func makeExpectedRptList(addresses []common.Address, expected int64) rpt.RptList {
	rptList := make([]rpt.Rpt, 0, len(addresses))
	for _, addr := range addresses {
		rptList = append(rptList, rpt.Rpt{Address: addr, Rpt: expected})
	}
	return rptList
}

func setPrimitiveMockValues(rank int64, txVolumn int64, maintenance int64, uploadCount int64, proxyCount int64, isProxy int64) {
	primitiveBackend.rank = rank
	primitiveBackend.txVolumn = txVolumn
	primitiveBackend.maintenance = maintenance
	primitiveBackend.uploadCount = uploadCount
	primitiveBackend.proxyCount = proxyCount
	primitiveBackend.isProxy = isProxy
}

// --- --- --- --- --- --- --- --- --- --- --- below are bench tests for new rpt calculation method --- --- --- --- --- --- --- --- --- --- ---

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

	rptCollector := rpt.NewRptCollectorImpl4(nil, fc)
	for i, addr := range addrs {
		rpt := rptCollector.RptOf(addr, addrs, 500)
		b.Log("idx", i, "rpt", rpt.Rpt, "addr", addr.Hex())
	}
}

func TestRptOf4(t *testing.T) {

	numAccount := 30
	numBlocks := 1000
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)

	rptCollector := rpt.NewRptCollectorImpl4(nil, fc)
	for i, addr := range accounts {
		rpt := rptCollector.RptOf(addr, accounts, 500)
		t.Log("idx", i, "rpt", rpt.Rpt, "addr", addr.Hex())
	}

}
func TestRptOf5(t *testing.T) {

	numAccount := 30
	numBlocks := 1000
	accounts := generateABatchAccounts(numAccount)
	fc := newFakeChainBackendForRptCollectorWithBalances(numBlocks, accounts)

	rptCollector := rpt.NewRptCollectorImpl5(nil, fc)
	for i, addr := range accounts {
		rpt := rptCollector.RptOf(addr, accounts, 500)
		t.Log("idx", i, "rpt", rpt.Rpt, "addr", addr.Hex())
	}

}
