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

	"crypto/rsa"

	"github.com/ethereum/go-ethereum/accounts/abi/bind"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/contracts/dpor/contract"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/crypto/rsa_"
	"github.com/ethereum/go-ethereum/log"
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

func DeploySignerConnectionRegister(transactOpts *bind.TransactOpts, contractBackend Backend) (common.Address, *types.Transaction, *SignerConnectionRegister, error) {
	contractAddr, tx, _, err := contract.DeploySignerConnectionRegister(transactOpts, contractBackend)
	if err != nil {
		return contractAddr, tx, nil, err
	}
	register, err := NewSignerConnectionRegister(transactOpts, contractAddr, contractBackend)
	if err != nil {
		return contractAddr, tx, nil, err
	}

	return contractAddr, tx, register, err
}

func (self *SignerConnectionRegister) GetPublicKey(addr common.Address) (*rsa.PublicKey, error) {
	publicKeyBytes, err := self.Contract.GetPublicKey(&self.CallOpts, addr)
	if err != nil {
		return nil, err
	}
	log.Info("address:%v,publicKeyBytes:%v", addr, publicKeyBytes)

	publicKey, err := rsa_.Bytes2PublicKey(publicKeyBytes)
	if err != nil {
		return nil, err
	}
	return publicKey, err
}

func (self *SignerConnectionRegister) GetNodeInfo(viewIndex *big.Int, privateKey *rsa.PrivateKey, otherAddress common.Address) (string, error) {
	encryptedNodeInfoBytesOnChain, err := self.Contract.GetNodeInfo(&self.CallOpts, viewIndex, otherAddress)
	if err != nil {
		return "", err
	}
	enode, err := rsa_.RsaDecrypt(encryptedNodeInfoBytesOnChain, privateKey)
	if err != nil {
		return "", err
	}
	return string(enode), nil
}

func (self *SignerConnectionRegister) RegisterPublicKey(rsaPublicKey []byte) (*types.Transaction, error) {
	self.TransactOpts.GasLimit = 300000
	self.TransactOpts.Value = big.NewInt(500)
	return self.Contract.RegisterPublicKey(&self.TransactOpts, rsaPublicKey)
}

func (self *SignerConnectionRegister) AddNodeInfo(viewIndex *big.Int, otherAddress common.Address, enode string) (*types.Transaction, error) {
	//  encrypt nodeInfo with other's RSA public key
	enodeBytes := []byte(enode)
	publicKey, err := self.GetPublicKey(otherAddress)
	if err != nil {
		return nil, err
	}
	encrpytedNodeInfo, err := rsa_.RsaEncrypt(enodeBytes, publicKey)
	if err != nil {
		return nil, err
	}
	return self.Contract.AddNodeInfo(&self.TransactOpts, viewIndex, otherAddress, encrpytedNodeInfo)
}
