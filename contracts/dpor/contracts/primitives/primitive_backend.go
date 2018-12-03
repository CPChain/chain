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

package primitives

// this package collects all reputation calculation related information,
// then calculates the reputations of candidates.

import (
	"context"
	"math/big"
	"sort"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	contract2 "bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"
	pdash "bitbucket.org/cpchain/chain/contracts/pdash/sol"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

//go:generate abigen --sol contracts/primitive_contracts_inst.sol --pkg contracts --out contracts/primitive_contracts_inst.go

var (
	extraVanity = 32 // Fixed number of extra-data prefix bytes reserved for signer vanity
	extraSeal   = 65 // Fixed number of extra-data suffix bytes reserved for signer seal
)

const (
	Created = iota
	Finished
)

type RptPrimitiveBackend interface {
	// Rank returns the rank for given account address at the given block number.
	Rank(address common.Address, number uint64) (int64, error)

	// TxVolume returns the transaction volumn for given account address at the given block number.
	TxVolume(address common.Address, number uint64) (int64, error)

	// Maintenance returns the maintenance score for given account address at the given block number.
	Maintenance(address common.Address, number uint64) (int64, error)

	// UploadCount returns the upload score for given account address at the given block number.
	UploadCount(address common.Address, number uint64) (int64, error)

	// ProxyInfo returns a value indicating whether the given address is proxy and the count of transactions processed
	// by the proxy at the given block number.
	ProxyInfo(address common.Address, number uint64) (isProxy int64, proxyCount int64, err error)
}

type RptEvaluator struct {
	Client backend.ClientBackend
}

func NewRptEvaluator(Client backend.ClientBackend) (*RptEvaluator, error) {
	bc := &RptEvaluator{
		Client: Client,
	}
	return bc, nil
}

// GetCoinAge is the func to get rank to rpt
func (re *RptEvaluator) Rank(address common.Address, number uint64) (int64, error) {
	var balances []float64
	myBalance, err := re.Client.BalanceAt(context.Background(), address, big.NewInt(int64(number)))
	if err != nil {
		log.Warn("error with getReputationnode", "error", err)
	}
	contractAddress := configs.MainnetChainConfig.Dpor.Contracts[configs.ContractCampaign]
	log.Info("campaign", "contractAddress", contractAddress)
	intance, err := contract2.NewCampaign(contractAddress, re.Client)
	if err != nil {
		log.Error("NewCampaign error", "error", err)
	}
	rNodeAddress, err := intance.CandidatesOf(nil, big.NewInt(int64(number)))
	if err != nil {
		log.Error("CandidatesOf error", "error", err)
	}
	for _, committee := range rNodeAddress {
		balance, err := re.Client.BalanceAt(context.Background(), committee, big.NewInt(int64(number)))
		if err != nil {
			log.Error("error with bc.BalanceAt", "error", err)
			return 0, err
		}
		balances = append(balances, float64(balance.Uint64()))
	}
	var rank int64
	sort.Sort(sort.Reverse(sort.Float64Slice(balances)))
	index := sort.SearchFloat64s(balances, float64(myBalance.Uint64()))
	rank = int64(index / 21)
	return rank, err
}

// GetCoinAge is the func to get txVolume to rpt
func (re *RptEvaluator) TxVolume(address common.Address, number uint64) (int64, error) {
	block, err := re.Client.BlockByNumber(context.Background(), big.NewInt(int64(number)))
	if err != nil {
		log.Error("error with bc.getTxVolume", "error", err)
		return 0, err
	}
	txvs := int64(0)
	signer := types.NewCep1Signer(configs.MainnetChainConfig.ChainID)
	txs := block.Transactions()
	for _, tx := range txs {
		sender, err := signer.Sender(tx)
		if err != nil {
			continue
		}
		if sender == address {
			//		txvs += float64(tx.Value().Uint64())
			txvs += 1
		}
	}
	return txvs, nil
}

// leader:0,committee:1,rNode:2,nil:3
func (re *RptEvaluator) Maintenance(address common.Address, number uint64) (int64, error) {
	ld := int64(2)
	ifRnode, err := re.RNode(address, number)
	if ifRnode != true {
		return 3, nil
	}
	if configs.MainnetChainConfig.ChainID.Uint64() == uint64(4) {
		return 0, nil
	}
	header, err := re.Client.HeaderByNumber(context.Background(), big.NewInt(int64(number)))
	if err != nil {
		log.Error("error with bc.getIfLeader", "error", err)
		return 0, err
	}
	number = number%configs.MainnetChainConfig.Dpor.TermLen - 1
	leader := header.Dpor.Proposers[number]

	log.Debug("leader.Hex is ", "hex", leader.Hex())

	if leader == address {
		ld = 0
	} else {
		for _, committee := range header.Dpor.Proposers {
			if address == committee {
				ld = 1
			}
		}
	}
	return ld, nil
}

// GetCoinAge is the func to get uploadnumber to rpt
func (re *RptEvaluator) UploadCount(address common.Address, number uint64) (int64, error) {
	uploadNumber := int64(0)
	contractAddress := configs.MainnetChainConfig.Dpor.Contracts[configs.ContractRegister]
	upload, err := pdash.NewRegister(contractAddress, re.Client)
	if err != nil {
		log.Error("NewRegister error", "error", err)
		return uploadNumber, err
	}
	fileNumber, err := upload.GetUploadCount(nil, address)
	if err != nil {
		log.Error("GetUploadCount error", "error", err)
		return uploadNumber, err
	}
	return fileNumber.Int64(), err
}

func (re *RptEvaluator) ProxyInfo(address common.Address, number uint64) (isProxy int64, proxyCount int64, err error) {
	proxyCount = int64(0)
	isProxy = int64(0)
	var proxyAddresses []common.Address
	contractAddress := configs.MainnetChainConfig.Dpor.Contracts[configs.ContractPdash]
	pdash, err := pdash.NewPdash(contractAddress, re.Client)

	if err != nil {
		log.Error("NewPdash error", "error", err)
		return proxyCount, 0, err
	}

	len, err := pdash.BlockOrdersLength(nil, big.NewInt(int64(number)))
	if err != nil {
		log.Error("BlockOrdersLength err", "error", err)
		return proxyCount, 0, err
	}

	for i := 0; i < int(len.Int64()); i++ {
		id, err := pdash.BlockOrders(nil, big.NewInt(int64(number)), big.NewInt(int64(i)))
		if err != nil {
			log.Error("BlockOrders error", "error", err)
			break
		}
		OrderRecord, err := pdash.OrderRecords(nil, id)
		proxyAddresses = append(proxyAddresses, OrderRecord.ProxyAddress)
	}

	for _, proxyAddress := range proxyAddresses {
		if proxyAddress == address {
			isProxy = 1
			break
		}
	}

	for i := 0; i < int(len.Int64()); i++ {
		id, err := pdash.BlockOrders(nil, big.NewInt(int64(number)), big.NewInt(int64(i)))
		if err != nil {
			log.Error("BlockOrders error", "error", err)
			break
		}
		OrderRecord, err := pdash.OrderRecords(nil, id)
		if OrderRecord.ProxyAddress == address && OrderRecord.State == Finished {
			proxyCount += 1
			if proxyCount == 100 {
				break
			}
		}
	}

	return isProxy, proxyCount, err
}

//func (re *RptEvaluator) CommitteeMember(header *types.Header) []common.Address {
//	committee := make([]common.Address, len(header.Dpor.Proposers))
//	for i := 0; i < len(committee); i++ {
//		copy(committee[i][:], header.Dpor.Proposers[i][:])
//	}
//	return committee
//}

func (re *RptEvaluator) RNode(address common.Address, number uint64) (bool, error) {
	contractAddress := configs.MainnetChainConfig.Dpor.Contracts[configs.ContractCampaign]
	instance, err := contract2.NewCampaign(contractAddress, re.Client)
	if err != nil {
		log.Error("NewCampaign error", "address", address, "error", err)
		return false, err
	}
	rNdoeAddress, err := instance.CandidatesOf(nil, big.NewInt(int64(number)))
	if err != nil {
		log.Error("CandidatesOf error", "error", err)
		return false, err
	}
	for _, rNode := range rNdoeAddress {
		if rNode == address {
			return true, nil
		}
	}
	return false, nil
}
