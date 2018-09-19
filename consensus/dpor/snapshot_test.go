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

package dpor

import (
	"reflect"
	"testing"

	"fmt"

	"encoding/json"

	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"bitbucket.org/cpchain/chain/core/types"
	"bitbucket.org/cpchain/chain/ethdb"
	"bitbucket.org/cpchain/chain/params"
	lru "github.com/hashicorp/golang-lru"
)

type fakeDb struct {
	dbType uint64
}

func (*fakeDb) Put(key []byte, value []byte) error {
	fmt.Println("executing db put")
	return nil
}

func (*fakeDb) Delete(key []byte) error {
	panic("implement me 1")
}

func (f *fakeDb) Get(key []byte) ([]byte, error) {
	fmt.Println("executing db put")
	if f.dbType == 1 {
		snap := new(DporSnapshot)
		blob, err := json.Marshal(snap)
		return blob, err
	}
	return []byte("ssss"), nil

}

func (*fakeDb) Has(key []byte) (bool, error) {
	panic("implement me3")
}

func (*fakeDb) Close() {
	panic("implement me4")
}

func (*fakeDb) NewBatch() ethdb.Batch {
	panic("implement me5")
}

func Test_newSnapshot(t *testing.T) {
	snap := newSnapshot(&params.DporConfig{Period: 3, Epoch: 3}, nil, 1, common.Hash{}, getSignerAddress())
	equal := reflect.DeepEqual(snap.signers(), getSignerAddress())
	if !equal {
		t.Errorf("expect %v,get %v", true, equal)
	}

	recents := snap.Recents
	if len(recents) != 0 {
		t.Errorf("expect 0 recents,get %v", len(recents))
	}

	candidates := snap.candidates()
	if len(candidates) != 0 {
		t.Errorf("expect 0 candidates,get %v", len(candidates))
	}
}

func Test_loadSnapshot(t *testing.T) {
	type args struct {
		config   *params.DporConfig
		sigcache *lru.ARCCache
		db       ethdb.Database
		hash     common.Hash
	}
	tests := []struct {
		name    string
		args    args
		want    *DporSnapshot
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := loadSnapshot(tt.args.config, tt.args.sigcache, tt.args.db, tt.args.hash)
			if (err != nil) != tt.wantErr {
				t.Errorf("loadSnapshot(%v, %v, %v, %v) error = %v, wantErr %v", tt.args.config, tt.args.sigcache, tt.args.db, tt.args.hash, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("loadSnapshot(%v, %v, %v, %v) = %v, want %v", tt.args.config, tt.args.sigcache, tt.args.db, tt.args.hash, got, tt.want)
			}
		})
	}
}

func TestSnapshot_store(t *testing.T) {

	type fields struct {
		config     *params.DporConfig
		sigcache   *lru.ARCCache
		Number     uint64
		Hash       common.Hash
		Signers    []common.Address
		Candidates []common.Address
		Recents    map[uint64]common.Address
	}
	type args struct {
		db ethdb.Database
	}

	cache, _ := lru.NewARC(inmemorySnapshots)
	config := &params.DporConfig{Period: 3, Epoch: 3}

	tests := []struct {
		name    string
		fields  fields
		args    args
		wantErr bool
	}{
		{"store ok",
			fields{config, cache, 1, common.Hash{},
				getSignerAddress(), getSignerAddress(), make(map[uint64]common.Address)},
			args{&fakeDb{}},
			false},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := &DporSnapshot{
				config:     tt.fields.config,
				sigcache:   tt.fields.sigcache,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Signers:    tt.fields.Signers,
				Candidates: tt.fields.Candidates,
				Recents:    tt.fields.Recents,
			}
			if err := s.store(tt.args.db); (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.store(%v) error = %v, wantErr %v", tt.args.db, err, tt.wantErr)
			}
		})
	}
}

func TestSnapshot_copy(t *testing.T) {
	snap := newSnapshot(&params.DporConfig{Period: 3, Epoch: 3}, nil, 1, common.Hash{}, getSignerAddress())
	snap.Candidates = getCandidates()
	snap.Recents = recents()

	cpySnap := snap.copy()

	equal := reflect.DeepEqual(cpySnap.signers(), getSignerAddress())
	if !equal {
		t.Errorf("expect %v,get %v", true, equal)
	}

	recents := cpySnap.Recents
	if len(recents) != 2 {
		t.Errorf("expect 2 recents,get %v", len(recents))
	}

	candidates := cpySnap.candidates()
	if len(candidates) != 3 {
		t.Errorf("expect 3 candidates,get %v", len(candidates))
	}
}

func TestSnapshot_apply(t *testing.T) {
	type fields struct {
		config     *params.DporConfig
		sigcache   *lru.ARCCache
		Number     uint64
		Hash       common.Hash
		Signers    []common.Address
		Candidates []common.Address
		Recents    map[uint64]common.Address
	}
	type args struct {
		headers []*types.Header
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		want    *DporSnapshot
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := &DporSnapshot{
				config:     tt.fields.config,
				sigcache:   tt.fields.sigcache,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Signers:    tt.fields.Signers,
				Candidates: tt.fields.Candidates,
				Recents:    tt.fields.Recents,
			}
			got, err := s.apply(tt.args.headers)
			if (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.apply(%v) error = %v, wantErr %v", tt.args.headers, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("DporSnapshot.apply(%v) = %v, want %v", tt.args.headers, got, tt.want)
			}
		})
	}
}

func TestSnapshot_applyHeader(t *testing.T) {
	type fields struct {
		config     *params.DporConfig
		sigcache   *lru.ARCCache
		Number     uint64
		Hash       common.Hash
		Signers    []common.Address
		Candidates []common.Address
		Recents    map[uint64]common.Address
	}
	type args struct {
		header *types.Header
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := &DporSnapshot{
				config:     tt.fields.config,
				sigcache:   tt.fields.sigcache,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Signers:    tt.fields.Signers,
				Candidates: tt.fields.Candidates,
				Recents:    tt.fields.Recents,
			}
			if err := s.applyHeader(tt.args.header); (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.applyHeader(%v) error = %v, wantErr %v", tt.args.header, err, tt.wantErr)
			}
		})
	}
}

func TestSnapshot_updateCandidates(t *testing.T) {
	type fields struct {
		config     *params.DporConfig
		sigcache   *lru.ARCCache
		Number     uint64
		Hash       common.Hash
		Signers    []common.Address
		Candidates []common.Address
		Recents    map[uint64]common.Address
	}
	type args struct {
		header *types.Header
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := &DporSnapshot{
				config:     tt.fields.config,
				sigcache:   tt.fields.sigcache,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Signers:    tt.fields.Signers,
				Candidates: tt.fields.Candidates,
				Recents:    tt.fields.Recents,
			}
			if err := s.updateCandidates(tt.args.header); (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.updateCandidates(%v) error = %v, wantErr %v", tt.args.header, err, tt.wantErr)
			}
		})
	}
}

func TestSnapshot_updateRpts(t *testing.T) {
	type fields struct {
		config     *params.DporConfig
		sigcache   *lru.ARCCache
		Number     uint64
		Hash       common.Hash
		Signers    []common.Address
		Candidates []common.Address
		Recents    map[uint64]common.Address
	}
	type args struct {
		header *types.Header
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		want    rpt.RPTs
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := &DporSnapshot{
				config:     tt.fields.config,
				sigcache:   tt.fields.sigcache,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Signers:    tt.fields.Signers,
				Candidates: tt.fields.Candidates,
				Recents:    tt.fields.Recents,
			}
			got, err := s.updateRpts(tt.args.header)
			if (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.updateRpts(%v) error = %v, wantErr %v", tt.args.header, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("DporSnapshot.updateRpts(%v) = %v, want %v", tt.args.header, got, tt.want)
			}
		})
	}
}

func TestSnapshot_updateView(t *testing.T) {
	type fields struct {
		config     *params.DporConfig
		sigcache   *lru.ARCCache
		Number     uint64
		Hash       common.Hash
		Signers    []common.Address
		Candidates []common.Address
		Recents    map[uint64]common.Address
	}
	type args struct {
		rpts       rpt.RPTs
		seed       int64
		viewLength int
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := &DporSnapshot{
				config:     tt.fields.config,
				sigcache:   tt.fields.sigcache,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Signers:    tt.fields.Signers,
				Candidates: tt.fields.Candidates,
				Recents:    tt.fields.Recents,
			}
			if err := s.updateView(tt.args.rpts, tt.args.seed, tt.args.viewLength); (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.updateView(%v, %v, %v) error = %v, wantErr %v", tt.args.rpts, tt.args.seed, tt.args.viewLength, err, tt.wantErr)
			}
		})
	}
}

func TestSnapshot_signers(t *testing.T) {
	snap := createSnapshot()
	signers := snap.signers()
	equalSigner := reflect.DeepEqual(signers, getSignerAddress())
	if !equalSigner {
		t.Errorf("expected isEqualSigner is %v,get %v", true, equalSigner)
	}
}

func TestSnapshot_signerRound(t *testing.T) {
	type fields struct {
		config     *params.DporConfig
		sigcache   *lru.ARCCache
		Number     uint64
		Hash       common.Hash
		Signers    []common.Address
		Candidates []common.Address
		Recents    map[uint64]common.Address
	}
	type args struct {
		signer common.Address
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		want    int
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := &DporSnapshot{
				config:     tt.fields.config,
				sigcache:   tt.fields.sigcache,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Signers:    tt.fields.Signers,
				Candidates: tt.fields.Candidates,
				Recents:    tt.fields.Recents,
			}
			got, err := s.signerRound(tt.args.signer)
			if (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.signerRound(%v) error = %v, wantErr %v", tt.args.signer, err, tt.wantErr)
				return
			}
			if got != tt.want {
				t.Errorf("DporSnapshot.signerRound(%v) = %v, want %v", tt.args.signer, got, tt.want)
			}
		})
	}
}

func TestSnapshot_isSigner(t *testing.T) {
	snap := newSnapshot(&params.DporConfig{Period: 3, Epoch: 3}, nil, 1, common.Hash{}, getSignerAddress()[1:2])
	isSinger := snap.isSigner(addr1)
	if isSinger {
		t.Errorf("expected isSinger %v,get %v", false, isSinger)
	}
	isSinger = snap.isSigner(addr2)
	if !isSinger {
		t.Errorf("expected isSinger %v,get %v", true, isSinger)
	}
}

func TestSnapshot_isLeaderErrorWhenBlockNumberIsZero(t *testing.T) {
	snap := createSnapshot()
	isLeader, err := snap.isLeader(addr1, 0)
	if err == nil {
		t.Errorf("expect isLeader Error, get %v", isLeader)
	}
}

func TestSnapshot_isLeader(t *testing.T) {
	snap := createSnapshot()
	isLeader, err := snap.isLeader(addr1, 1)
	if !isLeader || err != nil {
		t.Errorf("expect isLeader true, get %v", isLeader)
	}
	isLeader, err = snap.isLeader(addr2, 2)
	if !isLeader || err != nil {
		t.Errorf("expect isLeader true, get %v", isLeader)
	}
	isLeader, err = snap.isLeader(addr3, 3)
	if !isLeader || err != nil {
		t.Errorf("expect isLeader true, get %v", isLeader)
	}
}

func TestSnapshot_isNotLeader(t *testing.T) {
	snap := createSnapshot()
	isLeader, _ := snap.isLeader(addr2, 1)
	if isLeader {
		t.Errorf("expect isLeader false get %v", isLeader)
	}
	isLeader, _ = snap.isLeader(addr1, 2)
	if isLeader {
		t.Errorf("expect isLeader false get %v", isLeader)
	}
	isLeader, _ = snap.isLeader(addr1, 3)
	if isLeader {
		t.Errorf("expect isLeader false get %v", isLeader)
	}
}

func TestSnapshot_signerRoundFail(t *testing.T) {
	snap := createSnapshot()
	round, err := snap.signerRound(addr4)
	if err == nil || round != -1 {
		t.Errorf("expect round %v, get %v", -1, round)
	}
}

func TestSnapshot_signerRoundOk(t *testing.T) {
	snap := createSnapshot()
	round, err := snap.signerRound(addr1)
	if err != nil || round != 0 {
		t.Errorf("expect round %v, get %v", 0, round)
	}

	round, err = snap.signerRound(addr2)
	if err != nil || round != 1 {
		t.Errorf("expect round %v, get %v", 1, round)
	}

	round, err = snap.signerRound(addr3)
	if err != nil || round != 2 {
		t.Errorf("expect round %v, get %v", 2, round)
	}
}

func createSnapshot() *DporSnapshot {
	signers := getSignerAddress()
	config := &params.DporConfig{Period: 3, Epoch: 3}
	cache, _ := lru.NewARC(inmemorySnapshots)
	snap := newSnapshot(config, cache, 1, common.Hash{}, signers)
	return snap
}

func TestSnapshot_candidates(t *testing.T) {
	type fields struct {
		config     *params.DporConfig
		sigcache   *lru.ARCCache
		Number     uint64
		Hash       common.Hash
		Signers    []common.Address
		Candidates []common.Address
		Recents    map[uint64]common.Address
	}
	tests := []struct {
		name   string
		fields fields
		want   []common.Address
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := &DporSnapshot{
				config:     tt.fields.config,
				sigcache:   tt.fields.sigcache,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Signers:    tt.fields.Signers,
				Candidates: tt.fields.Candidates,
				Recents:    tt.fields.Recents,
			}
			if got := s.candidates(); !reflect.DeepEqual(got, tt.want) {
				t.Errorf("DporSnapshot.candidates() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestSnapshot_inturn(t *testing.T) {
	signers := getSignerAddress()
	config := &params.DporConfig{Period: 3, Epoch: 3}
	cache, _ := lru.NewARC(inmemorySnapshots)
	snap := newSnapshot(config, cache, 1, common.Hash{}, signers)

	tests := []struct {
		number         uint64
		addr           common.Address
		expectedResult bool
	}{
		{1, addr1, true},
		{1, addr2, false},
		{1, addr3, false},
		{2, addr1, false},
		{2, addr2, true},
		{2, addr3, false},
		{3, addr1, false},
		{3, addr2, false},
		{3, addr3, true},
		{4, addr1, true},
		{4, addr2, false},
		{4, addr3, false},
		{5, addr1, false},
		{5, addr2, true},
		{5, addr3, false},
	}

	for _, tt := range tests {
		inturn := snap.inturn(tt.number, tt.addr)
		if inturn != tt.expectedResult {
			t.Errorf("expected result is %v,get %v,number:%v,addr:%v", tt.expectedResult, inturn, tt.number, tt.addr)
		}
	}
}
