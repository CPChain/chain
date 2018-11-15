// Copyright 2016 The go-ethereum Authors
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

package dpor

import (
	"context"
	"fmt"
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

//go:generate abigen --sol rpt/rpt.sol --pkg rpt --out rpt/rpt.go

////go:generate abigen --sol contracts/campaign/campaign.sol --pkg contract --out contracts/campaign/campaign.go
//need generate in dir:contracts/dpor

// Backend wraps all methods required for campaign operation.
type Backend interface {
	bind.ContractBackend
	TransactionReceipt(ctx context.Context, txHash common.Hash) (*types.Receipt, error)
	BalanceAt(ctx context.Context, address common.Address, blockNum *big.Int) (*big.Int, error)
}

type CampaignWrapper struct {
	*campaign.CampaignSession
	contractBackend bind.ContractBackend
}

func NewCampaignWrapper(transactOpts *bind.TransactOpts, contractAddr common.Address, contractBackend Backend) (*CampaignWrapper, error) {
	c, err := campaign.NewCampaign(contractAddr, contractBackend)
	if err != nil {
		return nil, err
	}

	return &CampaignWrapper{
		&campaign.CampaignSession{
			Contract:     c,
			TransactOpts: *transactOpts,
		},
		contractBackend,
	}, nil
}

func DeployCampaign(transactOpts *bind.TransactOpts, contractBackend Backend, admissionContractAddr common.Address) (common.Address, *CampaignWrapper, error) {
	contractAddr, _, _, err := campaign.DeployCampaign(transactOpts, contractBackend, admissionContractAddr)
	if err != nil {
		return contractAddr, nil, err
	}
	campaign, err := NewCampaignWrapper(transactOpts, contractAddr, contractBackend)
	if err != nil {
		return contractAddr, nil, err
	}

	return contractAddr, campaign, err
}

func (self *CampaignWrapper) MaximumNoc() (*big.Int, error) {
	fmt.Println("MaximumNoc is called")
	return self.Contract.MaxNoc(nil)
}

func (self *CampaignWrapper) ClaimCampaign(numOfCampaign *big.Int, cpuNonce uint64, cpuBlockNumber *big.Int,
	memoryNonce uint64, memoryBlockNumber *big.Int) (*types.Transaction, error) {
	return self.Contract.ClaimCampaign(&self.TransactOpts, numOfCampaign, cpuNonce, cpuBlockNumber, memoryNonce, memoryBlockNumber)
}
