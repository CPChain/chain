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
	"crypto/ecdsa"
	"fmt"

	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/accounts/abi/bind"
	"github.com/ethereum/go-ethereum/accounts/abi/bind/backends"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/contracts/dpor/contract"
	"github.com/ethereum/go-ethereum/core"
)

func deployRegister(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	deployTransactor.Value = amount
	addr, _, _, err := contract.DeploySignerConnectionRegister(deployTransactor, backend)
	if err != nil {
		return common.Address{}, err
	}
	backend.Commit()
	return addr, nil
}

func TestDeploySignerConnectionRegister(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	contractAddr, err := deployRegister(key, big.NewInt(0), contractBackend)
	checkError(t, "deploy contract: expected no error, got %v", err)

	transactOpts := bind.NewKeyedTransactor(key)
	register, err := NewSignerConnectionRegister(transactOpts, contractAddr, contractBackend)
	checkError(t, "can't deploy root registry: %v", err)
	_ = contractAddr
	contractBackend.Commit()

	// ==================================================
	register.TransactOpts = *bind.NewKeyedTransactor(key)
	register.TransactOpts.GasLimit = 100000
	register.TransactOpts.GasPrice = big.NewInt(0)
	register.TransactOpts.Value = big.NewInt(1150)
	tx, err := register.AddNodeInfo(big.NewInt(1), addr, []byte("777"))
	checkError(t, "nodeInfo error: %v", err)
	contractBackend.Commit()

	// ==================================================
	nodeInfoBytes, err := register.GetNodeInfo(big.NewInt(1), addr)
	checkError(t, "nodeInfo error: %v", err)
	fmt.Println("nodeInfoBytes:", string(nodeInfoBytes))
	contractBackend.Commit()

	// =================================================
	var testme = "testmme"
	tx, err = register.RegisterPublicKey([]byte(testme))
	fmt.Println("RegisterPublicKey tx:", tx.Hash().Hex())
	contractBackend.Commit()
	// =================================================
	publicKey, err := register.GetPublicKey(addr)
	checkError(t, "publicKey error: %v", err)
	fmt.Println("publicKey:", publicKey, string(publicKey))
	if testme != string(publicKey) {
		t.Errorf("public key error,want:%v,got:%v", testme, string(publicKey))
	}
}
