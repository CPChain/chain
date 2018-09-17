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
	"math/big"

	"github.com/ethereum/go-ethereum/accounts/abi/bind"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/contracts/dpor/contract"
	"github.com/ethereum/go-ethereum/core/types"
)

//go:generate abigen --sol contract/signerRegister.sol --pkg contract --out contract/signerRegister.go

type SignerConnectionRegister struct {
	*contract.SignerConnectionRegisterSession
	contractBackend bind.ContractBackend
}

func NewSignerConnectionRegister(transactOpts *bind.TransactOpts, contractAddr common.Address, contractBackend Backend) (*SignerConnectionRegister, error) {
	c, err := contract.NewSignerConnectionRegister(contractAddr, contractBackend)
	if err != nil {
		return nil, err
	}

	return &SignerConnectionRegister{
		&contract.SignerConnectionRegisterSession{
			Contract:     c,
			TransactOpts: *transactOpts,
		},
		contractBackend,
	}, nil
}

func DeploySignerConnectionRegister(transactOpts *bind.TransactOpts, contractBackend Backend) (common.Address, *SignerConnectionRegister, error) {
	contractAddr, _, _, err := contract.DeploySignerConnectionRegister(transactOpts, contractBackend)
	if err != nil {
		return contractAddr, nil, err
	}
	register, err := NewSignerConnectionRegister(transactOpts, contractAddr, contractBackend)
	if err != nil {
		return contractAddr, nil, err
	}

	return contractAddr, register, err
}

func (self *SignerConnectionRegister) GetPublicKey(addr common.Address) ([]byte, error) {
	return self.Contract.GetPublicKey(&self.CallOpts, addr)
}

func (self *SignerConnectionRegister) GetNodeInfo(viewIndex *big.Int, otherAddress common.Address) ([]byte, error) {
	return self.Contract.GetNodeInfo(&self.CallOpts, viewIndex, otherAddress)
}

func (self *SignerConnectionRegister) RegisterPublicKey(rsaPublicKey []byte) (*types.Transaction, error) {
	return self.Contract.RegisterPublicKey(&self.TransactOpts, rsaPublicKey)
}

func (self *SignerConnectionRegister) AddNodeInfo(viewIndex *big.Int, otherAddress common.Address, encrpytedNodeInfo []byte) (*types.Transaction, error) {
	return self.Contract.AddNodeInfo(&self.TransactOpts, viewIndex, otherAddress, encrpytedNodeInfo)
}
