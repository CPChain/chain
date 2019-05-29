// Copyright 2015 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package cpc

import (
	"context"
	"math/big"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/bloombits"
	"bitbucket.org/cpchain/chain/core/rawdb"
	"bitbucket.org/cpchain/chain/core/state"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/protocols/cpc/gasprice"
	"bitbucket.org/cpchain/chain/protocols/cpc/syncer"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/math"
	"github.com/ethereum/go-ethereum/event"
)

// APIBackend implements cpcapi.Backend for full nodes
type APIBackend struct {
	cpc *CpchainService
	gpo *gasprice.Oracle
}

// ChainConfig returns the active chain configuration.
func (b *APIBackend) ChainConfig() *configs.ChainConfig {
	return b.cpc.chainConfig
}

func (b *APIBackend) CurrentBlock() *types.Block {
	return b.cpc.blockchain.CurrentBlock()
}

func (b *APIBackend) SetHead(number uint64) {
	b.cpc.blockchain.SetHead(number)
}

func (b *APIBackend) HeaderByNumber(ctx context.Context, blockNr rpc.BlockNumber) (*types.Header, error) {
	// Pending block is only known by the miner
	if blockNr == rpc.PendingBlockNumber {
		block := b.cpc.miner.PendingBlock()
		return block.Header(), nil
	}
	// Otherwise resolve and return the block
	if blockNr == rpc.LatestBlockNumber {
		return b.cpc.blockchain.CurrentBlock().Header(), nil
	}
	return b.cpc.blockchain.GetHeaderByNumber(uint64(blockNr)), nil
}

func (b *APIBackend) BlockByNumber(ctx context.Context, blockNr rpc.BlockNumber) (*types.Block, error) {
	// Pending block is only known by the miner
	if blockNr == rpc.PendingBlockNumber {
		block := b.cpc.miner.PendingBlock()
		return block, nil
	}
	// Otherwise resolve and return the block
	if blockNr == rpc.LatestBlockNumber {
		return b.cpc.blockchain.CurrentBlock(), nil
	}
	return b.cpc.blockchain.GetBlockByNumber(uint64(blockNr)), nil
}

func (b *APIBackend) StateAndHeaderByNumber(ctx context.Context, blockNr rpc.BlockNumber, isPrivate bool) (*state.StateDB, *types.Header, error) {
	// Pending state is only known by the miner
	if blockNr == rpc.PendingBlockNumber {
		block, state := b.cpc.miner.Pending()
		return state, block.Header(), nil
	}
	// Otherwise resolve the block number and return its state
	header, err := b.HeaderByNumber(ctx, blockNr)
	if header == nil || err != nil {
		return nil, nil, err
	}
	var stateDb *state.StateDB
	if isPrivate {
		stateDb, err = b.cpc.BlockChain().StatePrivAt(header.StateRoot)
	} else {
		stateDb, err = b.cpc.BlockChain().StateAt(header.StateRoot)
	}
	return stateDb, header, err
}

func (b *APIBackend) GetBlock(ctx context.Context, hash common.Hash) (*types.Block, error) {
	return b.cpc.blockchain.GetBlockByHash(hash), nil
}

func (b *APIBackend) GetReceipts(ctx context.Context, hash common.Hash) (types.Receipts, error) {
	if number := rawdb.ReadHeaderNumber(b.cpc.chainDb, hash); number != nil {
		return rawdb.ReadReceipts(b.cpc.chainDb, hash, *number), nil
	}
	return nil, nil
}

func (b *APIBackend) GetPrivateReceipt(ctx context.Context, txHash common.Hash) (*types.Receipt, error) {
	receipt, err := core.ReadPrivateReceipt(txHash, b.ChainDb())
	if err != nil {
		return nil, err
	}
	return receipt, nil
}

func (b *APIBackend) GetLogs(ctx context.Context, hash common.Hash) ([][]*types.Log, error) {
	number := rawdb.ReadHeaderNumber(b.cpc.chainDb, hash)
	if number == nil {
		return nil, nil
	}
	receipts := rawdb.ReadReceipts(b.cpc.chainDb, hash, *number)
	if receipts == nil {
		return nil, nil
	}
	logs := make([][]*types.Log, len(receipts))
	for i, receipt := range receipts {
		logs[i] = receipt.Logs
	}
	return logs, nil
}

func (b *APIBackend) GetEVM(ctx context.Context, msg core.Message, state *state.StateDB, header *types.Header, vmCfg vm.Config) (*vm.EVM, func() error, error) {
	state.SetBalance(msg.From(), math.MaxBig256)
	vmError := func() error { return nil }

	context := core.NewEVMContext(msg, header, b.cpc.BlockChain(), nil)
	return vm.NewEVM(context, state, b.cpc.chainConfig, vmCfg), vmError, nil
}

func (b *APIBackend) SubscribeRemovedLogsEvent(ch chan<- core.RemovedLogsEvent) event.Subscription {
	return b.cpc.BlockChain().SubscribeRemovedLogsEvent(ch)
}

func (b *APIBackend) SubscribeChainEvent(ch chan<- core.ChainEvent) event.Subscription {
	return b.cpc.BlockChain().SubscribeChainEvent(ch)
}

func (b *APIBackend) SubscribeChainHeadEvent(ch chan<- core.ChainHeadEvent) event.Subscription {
	return b.cpc.BlockChain().SubscribeChainHeadEvent(ch)
}

func (b *APIBackend) SubscribeChainSideEvent(ch chan<- core.ChainSideEvent) event.Subscription {
	return b.cpc.BlockChain().SubscribeChainSideEvent(ch)
}

func (b *APIBackend) SubscribeLogsEvent(ch chan<- []*types.Log) event.Subscription {
	return b.cpc.BlockChain().SubscribeLogsEvent(ch)
}

func (b *APIBackend) SendTx(ctx context.Context, signedTx *types.Transaction) error {
	return b.cpc.txPool.AddLocal(signedTx)
}

func (b *APIBackend) GetPoolTransactions() (types.Transactions, error) {
	pending, err := b.cpc.txPool.Pending()
	if err != nil {
		return nil, err
	}
	var txs types.Transactions
	for _, batch := range pending {
		txs = append(txs, batch...)
	}
	return txs, nil
}

func (b *APIBackend) GetPoolTransaction(hash common.Hash) *types.Transaction {
	return b.cpc.txPool.Get(hash)
}

func (b *APIBackend) GetPoolNonce(ctx context.Context, addr common.Address) (uint64, error) {
	return b.cpc.txPool.State().GetNonce(addr), nil
}

func (b *APIBackend) Stats() (pending int, queued int) {
	return b.cpc.txPool.Stats()
}

func (b *APIBackend) TxPoolContent() (map[common.Address]types.Transactions, map[common.Address]types.Transactions) {
	return b.cpc.TxPool().Content()
}

func (b *APIBackend) SubscribeNewTxsEvent(ch chan<- core.NewTxsEvent) event.Subscription {
	return b.cpc.TxPool().SubscribeNewTxsEvent(ch)
}

func (b *APIBackend) Downloader() syncer.Syncer {
	return b.cpc.Downloader()
}

func (b *APIBackend) ProtocolVersion() int {
	return b.cpc.CpcVersion()
}

func (b *APIBackend) SuggestPrice(ctx context.Context) (*big.Int, error) {
	return b.gpo.SuggestPrice(ctx)
}

func (b *APIBackend) ChainDb() database.Database {
	return b.cpc.ChainDb()
}

func (b *APIBackend) EventMux() *event.TypeMux {
	return b.cpc.EventMux()
}

func (b *APIBackend) AccountManager() *accounts.Manager {
	return b.cpc.AccountManager()
}

func (b *APIBackend) BloomStatus() (uint64, uint64) {
	sections, _, _ := b.cpc.bloomIndexer.Sections()
	return configs.BloomBitsBlocks, sections
}

func (b *APIBackend) ServiceFilter(ctx context.Context, session *bloombits.MatcherSession) {
	for i := 0; i < bloomFilterThreads; i++ {
		go session.Multiplex(bloomRetrievalBatch, bloomRetrievalWait, b.cpc.bloomRequests)
	}
}

// RemoteDB returns remote database instance.
func (b *APIBackend) RemoteDB() database.RemoteDatabase {
	return b.cpc.RemoteDB()
}

// RNode returns current RNode information
func (b *APIBackend) RNode() ([]common.Address, uint64) {
	block := b.cpc.blockchain.CurrentBlock()
	bn := block.Number()
	api := b.cpc.engine.(*dpor.Dpor).APIs(b.cpc.blockchain)
	rNodes, _ := api[0].Service.(*dpor.API).GetRNodes()
	return rNodes, bn.Uint64()
}

// CurrentView return current view
func (b *APIBackend) CurrentView() uint64 {
	block := b.cpc.blockchain.CurrentBlock()
	bn := block.Number()
	vl, tl := b.ViewLen(), b.TermLen()
	// be cautious vl*tl does not overflow
	view := ((bn.Uint64() - 1) % (vl * tl)) / vl
	return view
}

// CurrentSpan return current span
func (b *APIBackend) CurrentSpan() uint64 {
	block := b.cpc.blockchain.CurrentBlock()
	bn := block.Number()
	vl, tl := b.ViewLen(), b.TermLen()
	span := ((bn.Uint64() - 1) % (vl * tl)) % tl
	return span
}

// CurrentTerm return current term
func (b *APIBackend) CurrentTerm() uint64 {
	block := b.cpc.blockchain.CurrentBlock()
	bn := block.Number()
	vl, tl := b.ViewLen(), b.TermLen()
	term := (bn.Uint64() - 1) / (vl * tl)
	return term
}

// ViewLen return current ViewLen
func (b *APIBackend) ViewLen() uint64 {
	return b.cpc.chainConfig.Dpor.ViewLen
}

// TermLen return current TermLen
func (b *APIBackend) TermLen() uint64 {
	return b.cpc.chainConfig.Dpor.TermLen
}

// CommitteMember return current committe
func (b *APIBackend) CommitteMember() []common.Address {
	block := b.cpc.blockchain.CurrentBlock()
	return block.Header().Dpor.Proposers
}

func (b *APIBackend) CalcRptInfo(address common.Address, addresses []common.Address, blockNum uint64) int64 {
	return b.cpc.engine.(*dpor.Dpor).GetCalcRptInfo(address, addresses, blockNum)
}

func (b *APIBackend) BlockReward(blockNum rpc.BlockNumber) *big.Int {
	return b.cpc.engine.(*dpor.Dpor).GetBlockReward(uint64(blockNum))
}

func (b *APIBackend) ProposerOf(blockNum rpc.BlockNumber) (common.Address, error) {
	p, err := b.cpc.engine.(*dpor.Dpor).ProposerOf(uint64(blockNum))
	return p, err
}

// Proposers returns current block Proposers information
func (b *APIBackend) Proposers(blockNr rpc.BlockNumber) ([]common.Address, error) {
	api := b.cpc.engine.(*dpor.Dpor).APIs(b.cpc.blockchain)
	return api[0].Service.(*dpor.API).GetProposers(blockNr)
}

// Validators returns current block Validators information
func (b *APIBackend) Validators(blockNr rpc.BlockNumber) ([]common.Address, error) {
	api := b.cpc.engine.(*dpor.Dpor).APIs(b.cpc.blockchain)
	return api[0].Service.(*dpor.API).GetValidators(blockNr)
}

func (b *APIBackend) SupportPrivateTx(ctx context.Context) (bool, error) {
	return core.SupportPrivateTx(b.cpc.blockchain), nil
}
