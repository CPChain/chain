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

//go:generate abigen --sol contract/campaign.sol --pkg contract --out contract/campaign.go

import (
	"context"
	"fmt"

	"math/big"

	"github.com/ethereum/go-ethereum/accounts/abi/bind"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/contracts/dpor/contract"
	"github.com/ethereum/go-ethereum/core/types"
)

// Backend wraps all methods required for chequebook operation.
type Backend interface {
	bind.ContractBackend
	TransactionReceipt(ctx context.Context, txHash common.Hash) (*types.Receipt, error)
	BalanceAt(ctx context.Context, address common.Address, blockNum *big.Int) (*big.Int, error)
}

// swarm domain name registry and resolver
type Campaign struct {
	*contract.CampaignSession
	contractBackend bind.ContractBackend
}

func NewCampaign(transactOpts *bind.TransactOpts, contractAddr common.Address, contractBackend Backend) (*Campaign, error) {
	c, err := contract.NewCampaign(contractAddr, contractBackend)
	if err != nil {
		return nil, err
	}

	return &Campaign{
		&contract.CampaignSession{
			Contract:     c,
			TransactOpts: *transactOpts,
		},
		contractBackend,
	}, nil
}

func DeployCampaign(transactOpts *bind.TransactOpts, contractBackend Backend) (common.Address, *Campaign, error) {
	contractAddr, _, _, err := contract.DeployCampaign(transactOpts, contractBackend)
	if err != nil {
		return contractAddr, nil, err
	}
	campaign, err := NewCampaign(transactOpts, contractAddr, contractBackend)
	if err != nil {
		return contractAddr, nil, err
	}

	return contractAddr, campaign, err
}

func (self *Campaign) MaximumNoc() (*big.Int, error) {
	fmt.Println("MaximumNoc is called")
	return self.Contract.MaximumNoc(nil)
}

func (self *Campaign) ClaimCampaign(numOfCampaign *big.Int, rpt *big.Int) (*types.Transaction, error) {
	return self.Contract.ClaimCampaign(&self.TransactOpts, numOfCampaign, rpt)
}
