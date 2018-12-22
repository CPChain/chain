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

package dpor

import (
	"fmt"
	"math/big"
	"reflect"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	lru "github.com/hashicorp/golang-lru"
)

func Test_dporHelper_verifyHeader(t *testing.T) {
	t.Skip("need to redesign the unittests for dporHelper")

	dh := &defaultDporHelper{}

	extraErr1 := "0x00000000000000000000000000000000"
	fmt.Println("extraErr1:", extraErr1)

	rightExtra := "0x0000000000000000000000000000000000000000000000000000000000000000"
	rightSeal := "0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"
	rightAddr := "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"

	time1 := big.NewInt(time.Now().Unix() + 100)
	time := big.NewInt(time.Now().Unix() - 100)

	type args struct {
		c         *Dpor
		chain     consensus.ChainReader
		header    *types.Header
		parents   []*types.Header
		refHeader *types.Header
	}
	tests := []struct {
		name    string
		d       *defaultDporHelper
		args    args
		wantErr bool
	}{
		{"header.Number is nil", dh, args{header: &types.Header{Number: nil, Time: time1}}, true},

		{"header.Time error", dh, args{header: &types.Header{Number: big.NewInt(6),
			Time: time1}}, true},

		{"errInvalidCheckpointBeneficiary", dh,
			args{header: &types.Header{Number: big.NewInt(6), Time: time, Coinbase: common.HexToAddress("aaaaa")},
				c: &Dpor{config: &configs.DporConfig{TermLen: 3}}}, true},

		{"header.Extra error1", dh,
			args{
				header: &types.Header{
					Number: big.NewInt(5), Time: time, Extra: hexutil.MustDecode(string(extraErr1))},
				c: &Dpor{config: &configs.DporConfig{TermLen: 3}}}, true},

		{"errInvalidDifficulty", dh,
			args{
				header: &types.Header{
					Number: big.NewInt(7),
					Time:   time,
					Extra:  hexutil.MustDecode(string(rightExtra)),
					Dpor: types.DporSnap{
						Seal: types.HexToDporSig(rightSeal),
						Proposers: []common.Address{
							common.HexToAddress(rightAddr),
						},
					}},
				c: &Dpor{config: &configs.DporConfig{TermLen: 3}}}, true},

		{"success", dh,
			args{
				header: &types.Header{
					Number: big.NewInt(0),
					Time:   time,
					Extra:  hexutil.MustDecode(string(rightExtra)),
					Dpor: types.DporSnap{
						Seal: types.HexToDporSig(rightSeal),
						Proposers: []common.Address{
							common.HexToAddress(rightAddr),
						},
					},
					Difficulty: big.NewInt(2)},
				c:       &Dpor{config: &configs.DporConfig{TermLen: 3}, dh: &defaultDporHelper{}},
				chain:   &FakeReader{},
				parents: []*types.Header{},
			}, false},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			dh := &defaultDporHelper{}
			if err := dh.verifyHeader(tt.args.c, tt.args.chain, tt.args.header, tt.args.parents, tt.args.refHeader, true, false); (err != nil) != tt.wantErr {
				t.Errorf("defaultDporHelper.verifyHeader(%v, %v, %v, %v, %v) error = %v, wantErr %v", tt.args.c, tt.args.chain, tt.args.header, tt.args.parents, tt.args.refHeader, err, tt.wantErr)
			}
		})
	}
}

func Test_dporHelper_verifyCascadingFields(t *testing.T) {
	t.Skip("need to redesign the unittests for dporHelper")

	recents, _ := lru.NewARC(10)
	rightExtra := "0x0000000000000000000000000000000000000000000000000000000000000000"
	seal := "0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"
	proposer := "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"
	time1 := big.NewInt(time.Now().Unix() - 100)
	time2 := big.NewInt(time.Now().Unix() + 100)
	header := &types.Header{Number: big.NewInt(0), Time: time1}
	parentHash := header.Hash()
	recents.Add(parentHash, &DporSnapshot{config: &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 3}, RecentSigners: make(map[uint64][]common.Address)})
	chain := &FakeReader{}
	type args struct {
		d         *Dpor
		chain     consensus.ChainReader
		header    *types.Header
		parents   []*types.Header
		refHeader *types.Header
	}
	tests := []struct {
		name    string
		d       *defaultDporHelper
		args    args
		wantErr bool
	}{
		{"success when block 0", &defaultDporHelper{},
			args{d: &Dpor{recentSnaps: recents, config: &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 4}},
				header: &types.Header{Number: big.NewInt(0), ParentHash: parentHash}, chain: chain}, false},
		{"fail with parent block", &defaultDporHelper{},
			args{d: &Dpor{recentSnaps: recents, config: &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 4}},
				header:  &types.Header{Number: big.NewInt(1), ParentHash: parentHash, Time: time1},
				parents: []*types.Header{header}, chain: chain}, true},
		{"errInvalidSigners", &defaultDporHelper{},
			args{d: &Dpor{recentSnaps: recents, config: &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 4}, dh: &defaultDporHelper{}},
				header: &types.Header{Number: big.NewInt(1), ParentHash: parentHash, Time: time2,
					Extra: hexutil.MustDecode(rightExtra), Dpor: types.DporSnap{Seal: types.HexToDporSig(seal),
						Proposers: []common.Address{common.HexToAddress(proposer)}},
				},
				parents: []*types.Header{header}, chain: chain}, true},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			d := &defaultDporHelper{}
			if err := d.verifyProposers(tt.args.d, tt.args.chain, tt.args.header, tt.args.parents, tt.args.refHeader); (err != nil) != tt.wantErr {
				t.Errorf("defaultDporHelper.verifyProposers(%v, %v, %v, %v, %v) error = %v, wantErr %v", tt.args.d, tt.args.chain, tt.args.header, tt.args.parents, tt.args.refHeader, err, tt.wantErr)
			}
		})
	}
}

func Test_dporHelper_snapshot(t *testing.T) {
	type args struct {
		c       *Dpor
		chain   consensus.ChainReader
		number  uint64
		hash    common.Hash
		parents []*types.Header
	}
	tests := []struct {
		name    string
		d       *defaultDporHelper
		args    args
		want    *DporSnapshot
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			d := &defaultDporHelper{}
			got, err := d.snapshot(tt.args.c, tt.args.chain, tt.args.number, tt.args.hash, tt.args.parents)
			if (err != nil) != tt.wantErr {
				t.Errorf("defaultDporHelper.Snapshot(%v, %v, %v, %v, %v) error = %v, wantErr %v", tt.args.c, tt.args.chain, tt.args.number, tt.args.hash, tt.args.parents, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("defaultDporHelper.Snapshot(%v, %v, %v, %v, %v) = %v, want %v", tt.args.c, tt.args.chain, tt.args.number, tt.args.hash, tt.args.parents, got, tt.want)
			}
		})
	}
}

func Test_dporHelper_verifySeal(t *testing.T) {

	rightExtra := "0x0000000000000000000000000000000000000000000000000000000000000000"
	rightAddr := "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"
	rightSeal := "0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"

	time1 := big.NewInt(time.Now().Unix() - 100)

	header := &types.Header{Number: big.NewInt(0), Time: time1}
	parentHash := header.Hash()
	recents, _ := lru.NewARC(10)
	recents.Add(parentHash, &DporSnapshot{})
	//rightExtra2 := "0x00c9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00c9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00c9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"

	type args struct {
		c         *Dpor
		chain     consensus.ChainReader
		header    *types.Header
		parents   []*types.Header
		refHeader *types.Header
	}
	tests := []struct {
		name    string
		d       *defaultDporHelper
		args    args
		wantErr bool
	}{
		// TODO: Add test cases.
		{"fail when block number is 0", &defaultDporHelper{},
			args{
				c: &Dpor{
					config:      &configs.DporConfig{Period: 3},
					db:          &fakeDb{1},
					recentSnaps: recents, dh: &defaultDporHelper{}},
				chain: &FakeReader{},
				header: &types.Header{
					Number: big.NewInt(0),
					Time:   time1,
					Extra:  hexutil.MustDecode(string(rightExtra)),
					Dpor: types.DporSnap{
						Proposers: []common.Address{
							common.HexToAddress(rightAddr),
						},
						Seal: types.HexToDporSig(rightSeal),
					},
					Difficulty: big.NewInt(2)}},
			true},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if err := tt.d.verifySeal(tt.args.c, tt.args.chain, tt.args.header, tt.args.parents, tt.args.refHeader); (err != nil) != tt.wantErr {
				t.Errorf("defaultDporHelper.verifySeal(%v, %v, %v, %v, %v) error = %v, wantErr %v", tt.args.c, tt.args.chain, tt.args.header, tt.args.parents, tt.args.refHeader, err, tt.wantErr)
			}
		})
	}
}
