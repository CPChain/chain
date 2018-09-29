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

package proxy

import (
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/contracts/proxy/contract"
	"bitbucket.org/cpchain/chain/core/types"
	"bitbucket.org/cpchain/chain/log"
)

//go:generate abigen --sol contract/proxyContractRegister.sol --pkg contract --out contract/proxyContractRegister.go

type ProxyContractRegister struct {
	*contract.ProxyContractRegisterSession
	contractBackend bind.ContractBackend
}

func NewProxyContractRegister(transactOpts *bind.TransactOpts, contractAddr common.Address, contractBackend Backend) (*ProxyContractRegister, error) {
	c, err := contract.NewProxyContractRegister(contractAddr, contractBackend)
	if err != nil {
		return nil, err
	}

	return &ProxyContractRegister{
		&contract.ProxyContractRegisterSession{
			Contract:     c,
			TransactOpts: *transactOpts,
		},
		contractBackend,
	}, nil
}

func DeployProxyContractRegister(transactOpts *bind.TransactOpts, contractBackend Backend) (common.Address, *types.Transaction, *ProxyContractRegister, error) {
	contractAddr, tx, _, err := contract.DeployProxyContractRegister(transactOpts, contractBackend)
	if err != nil {
		return contractAddr, tx, nil, err
	}
	register, err := NewProxyContractRegister(transactOpts, contractAddr, contractBackend)
	if err != nil {
		return contractAddr, tx, nil, err
	}

	return contractAddr, tx, register, err
}

func (self *ProxyContractRegister) GetRealContract(addr common.Address) (common.Address, error) {
	realAddress, err := self.Contract.GetRealContract(&self.CallOpts, addr)
	if err != nil {
		return common.Address{}, err
	}
	log.Info("address:%v,realAddress:%v", addr, realAddress.Hex())
	return realAddress, err
}

func (self *ProxyContractRegister) RegisterPublicKey(proxyAddress, realAddress common.Address) (*types.Transaction, error) {
	self.TransactOpts.GasLimit = 300000
	self.TransactOpts.Value = big.NewInt(500)
	return self.Contract.RegisterProxyContract(&self.TransactOpts, proxyAddress, realAddress)
}
