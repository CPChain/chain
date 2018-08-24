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
	"testing"

	"reflect"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/params"
)

func TestNewSnapshot(t *testing.T) {
	snap := newSnapshot(&params.DporConfig{Period: 3, Epoch: 3}, nil, 1, common.Hash{}, getSignerAddress())
	equal := reflect.DeepEqual(snap.signers(), getSignerAddress())
	if !equal {
		t.Errorf("expect %v,get %v", true, equal)
	}

	recents := snap.Recents
	if len(recents) != 0 {
		t.Errorf("expect 0 recents,get %v", len(recents))
	}

	candidates := snap.Candidates
	if len(candidates) != 0 {
		t.Errorf("expect 0 candidates,get %v", len(candidates))
	}
}

func TestCopySnapshot(t *testing.T) {
	snap := newSnapshot(&params.DporConfig{Period: 3, Epoch: 3}, nil, 1, common.Hash{}, getSignerAddress())
	snap.Candidates = getCandidates()
	snap.Recents = getRecents()

	cpySnap := snap.copy()

	equal := reflect.DeepEqual(cpySnap.signers(), getSignerAddress())
	if !equal {
		t.Errorf("expect %v,get %v", true, equal)
	}

	recents := cpySnap.Recents
	if len(recents) != 2 {
		t.Errorf("expect 2 recents,get %v", len(recents))
	}

	candidates := cpySnap.Candidates
	if len(candidates) != 3 {
		t.Errorf("expect 3 candidates,get %v", len(candidates))
	}
}

// TODO test me later
func TestApplyHeader(t *testing.T) {
	t.Skip("test me later")
}

func TestUpdateCandidates(t *testing.T) {
	t.Skip("not implemented,test me later")
}

func TestUpdateRpts(t *testing.T) {
	t.Skip("not implemented,test me later")
}

func TestUpdateView(t *testing.T) {
	t.Skip("not implemented,test me later")
}

func TestCalcElection(t *testing.T) {
	t.Skip("not implemented,test me later")
}

func TestInturn(t *testing.T) {
	snap := newSnapshot(&params.DporConfig{Period: 3, Epoch: 3}, nil, 1, common.Hash{}, getSignerAddress())
	tests := []struct {
		number         uint64
		addr           common.Address
		expectedResult bool
	}{
		{0, addr1, true},
		{0, addr2, false},
		{0, addr3, false},
		{1, addr1, false},
		{1, addr2, true},
		{1, addr3, false},
		{2, addr1, false},
		{2, addr2, false},
		{2, addr3, true},
		{3, addr1, true},
		{3, addr2, false},
		{3, addr3, false},
		{4, addr1, false},
		{4, addr2, true},
		{4, addr3, false},
		{5, addr1, false},
		{5, addr2, false},
		{5, addr3, true},
	}

	for _, tt := range tests {
		assertInturn(snap, t, tt.number, tt.addr, tt.expectedResult)
	}
}

func assertInturn(snap *Snapshot, t *testing.T, number uint64, addr common.Address, expectedResult bool) {
	inturn := snap.inturn(number, addr)
	if inturn != expectedResult {
		t.Errorf("expected result is %v,get %v,number:%v,addr:%v", expectedResult, inturn, number, addr)
	}
}

func TestIsSigner(t *testing.T) {
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

func TestSigners(t *testing.T) {
	snap := newSnapshot(&params.DporConfig{Period: 3, Epoch: 3}, nil, 1, common.Hash{}, getSignerAddress())
	signers := snap.signers()
	equalSigner := reflect.DeepEqual(signers, getSignerAddress())
	if !equalSigner {
		t.Errorf("expected isEqualSigner is %v,get %v", true, equalSigner)
	}
}

func TestIsLeader(t *testing.T) {
	isLeader := snapIsLeader(addr1)
	if !isLeader {
		t.Errorf("expect isLeader true, get %v", isLeader)
	}
}

func TestIsNotLeader(t *testing.T) {
	isLeader := snapIsLeader(addr2)
	if isLeader {
		t.Errorf("expect isLeader false get %v", isLeader)
	}
	isLeader = snapIsLeader(addr3)
	if isLeader {
		t.Errorf("expect isLeader false get %v", isLeader)
	}
}

func snapIsLeader(leader common.Address) bool {
	signers := getSigners()
	snap := &Snapshot{config: &params.DporConfig{Period: 3, Epoch: 3}, Signers: signers,
		Number: 1}
	isLeader := snap.isLeader(0, leader)
	return isLeader
}
