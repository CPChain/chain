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
	"fmt"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
	lru "github.com/hashicorp/golang-lru"
)

var (
	addr1 = common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465")
	addr2 = common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092")
	addr3 = common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")
	addr4 = common.HexToAddress("0x3333333333333333333333333333333333333333")
)

func getSignerAddress() []common.Address {
	signersAddr := make([]common.Address, 3)
	signersAddr[0] = addr1
	signersAddr[1] = addr2
	signersAddr[2] = addr3
	return signersAddr
}

func getCandidates() []common.Address {
	return getSignerAddress()
}

func getRecents() map[uint64]common.Address {
	signers := make(map[uint64]common.Address)
	signers[0] = addr1
	signers[1] = addr2
	return signers
}

func TestAcceptSigsShouldBeFalse(t *testing.T) {
	signersAddr := getSignerAddress()
	cache, _ := lru.NewARC(inmemorySnapshots)
	accept1 := acceptHeaderSigs(cache, addr1, signersAddr[1:2], signersAddr)
	if accept1 {
		t.Errorf("Accept Sigs Should Be False")
	}
}

func TestAcceptSigsShouldBeTrue(t *testing.T) {
	signersAddr := getSignerAddress()
	cache, _ := lru.NewARC(inmemorySnapshots)
	accept1 := acceptHeaderSigs(cache, addr1, signersAddr, signersAddr)
	if !accept1 {
		t.Errorf("Accept Sigs Should Be True")
	}
}

func acceptHeaderSigs(cache *lru.ARCCache, coinbase common.Address, signerAddres []common.Address, signersAddr []common.Address) bool {
	header := &types.Header{
		Coinbase:    coinbase,
		Number:      big.NewInt(1),
		Difficulty:  big.NewInt(int64(1)),
		UncleHash:   types.EmptyUncleHash,
		TxHash:      types.EmptyRootHash,
		ReceiptHash: types.EmptyRootHash,
	}
	sigs := make(map[common.Address][]byte)
	for _, signer := range signerAddres {
		sigs[signer] = []byte("ok")
	}
	cache.Add(header.Hash(), sigs)

	accept, _ := acceptSigs(header, cache, signersAddr)
	return accept
}

func TestCalcDifficultyWhenSnapshotIsNotLeader(t *testing.T) {
	signers := getSignerAddress()
	cache, _ := lru.NewARC(inmemorySnapshots)
	config := &params.DporConfig{Period: 3, Epoch: 3}
	snapshot := newSnapshot(config, cache, 1, common.Hash{}, signers)
	result := CalcDifficulty(snapshot, signers[0])
	fmt.Println("TestCalcDifficulty result:", result)
	if big.NewInt(1).Cmp(result) != 0 {
		t.Errorf("expect:%d, but get: %v", 1, result)
	}
}

func TestCalcDifficultyWhenSnapshotIsLeader(t *testing.T) {
	signers := getSignerAddress()
	config := &params.DporConfig{Period: 3, Epoch: 3}
	cache, _ := lru.NewARC(inmemorySnapshots)
	snapshot := newSnapshot(config, cache, 1, common.Hash{}, signers)
	result := CalcDifficulty(snapshot, signers[1])
	fmt.Println("TestCalcDifficultyWhenSnapshotIsLeader result:", result)
	if big.NewInt(2).Cmp(result) != 0 {
		t.Errorf("expect:%d, but get: %v", 2, result)
	}
}

func Test_percentagePBFT(t *testing.T) {
	type args struct {
		n uint
		N uint
	}
	tests := []struct {
		name string
		args args
		want bool
	}{
		// TODO: Add test cases.
		{"0", args{0, 21}, false},
		{"14", args{14, 21}, false},
		{"15", args{15, 21}, true},
		{"21", args{21, 21}, true},
		{"1000", args{1000, 21}, true},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := percentagePBFT(tt.args.n, tt.args.N); got != tt.want {
				t.Errorf("percentagePBFT() = %v, want %v", got, tt.want)
			}
		})
	}
}
