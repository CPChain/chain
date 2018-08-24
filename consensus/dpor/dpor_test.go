// Copyright 2017 The go-ethereum Authors
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

// Package dpor implements the dpor consensus engine.
package dpor

import (
	"testing"

	"math/big"

	"fmt"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
	"github.com/hashicorp/golang-lru"
)

var (
	addr1 = common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465")
	addr2 = common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092")
	addr3 = common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")
)

func getSigners() map[uint64]common.Address {
	signers := make(map[uint64]common.Address)
	signers[0] = addr1
	signers[1] = addr2
	signers[2] = addr3
	return signers
}

func getSignerAddress() []common.Address {
	signersAddr := make([]common.Address, 3)
	signersAddr[0] = addr1
	signersAddr[1] = addr2
	signersAddr[2] = addr3
	return signersAddr
}

func getCandidates() map[common.Address]struct{} {
	candidates := make(map[common.Address]struct{}, 3)
	candidates[addr1] = struct{}{}
	candidates[addr2] = struct{}{}
	candidates[addr3] = struct{}{}
	return candidates
}

func getRecents() map[uint64]common.Address {
	signers := make(map[uint64]common.Address)
	signers[0] = addr1
	signers[1] = addr2
	return signers
}

func TestAcceptSigsShouldBeTrue(t *testing.T) {
	signersAddr := getSignerAddress()
	cache, _ := lru.NewARC(inmemorySnapshots)
	header := &types.Header{
		Coinbase:    addr1,
		Number:      big.NewInt(1),
		Difficulty:  big.NewInt(int64(1)),
		UncleHash:   types.EmptyUncleHash,
		TxHash:      types.EmptyRootHash,
		ReceiptHash: types.EmptyRootHash,
	}
	accept, _ := acceptSigs(header, cache, signersAddr)
	if accept {
		t.Errorf("Accept Sigs Should Be True")
	}
}

func TestAcceptSigsShouldBeFalse(t *testing.T) {
	signersAddr := getSignerAddress()
	cache, _ := lru.NewARC(inmemorySnapshots)
	header := &types.Header{
		Coinbase:    addr1,
		Number:      big.NewInt(1),
		Difficulty:  big.NewInt(int64(1)),
		UncleHash:   types.EmptyUncleHash,
		TxHash:      types.EmptyRootHash,
		ReceiptHash: types.EmptyRootHash,
	}
	accept, _ := acceptSigs(header, cache, signersAddr)
	if !accept {
		t.Errorf("Accept Sigs Should Be False")
	}

}

func TestCalcDifficultyWhenSnapshotIsNotLeader(t *testing.T) {
	signers := getSigners()
	result := CalcDifficulty(
		&Snapshot{config: &params.DporConfig{Period: 3, Epoch: 3}, Signers: signers,
			Number: 1}, signers[0])
	fmt.Println("TestCalcDifficulty result:", result)
	if big.NewInt(1).Cmp(result) != 0 {
		t.Errorf("expect:%d, but get: %v", 1, result)
	}
}

func TestCalcDifficultyWhenSnapshotIsLeader(t *testing.T) {
	signers := getSigners()
	result := CalcDifficulty(
		&Snapshot{config: &params.DporConfig{Period: 3, Epoch: 3}, Signers: signers,
			Number: 1}, signers[1])
	fmt.Println("TestCalcDifficultyWhenSnapshotIsLeader result:", result)
	if big.NewInt(2).Cmp(result) != 0 {
		t.Errorf("expect:%d, but get: %v", 2, result)
	}
}
