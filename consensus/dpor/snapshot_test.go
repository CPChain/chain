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

func TestIsLeader(t *testing.T) {
	isLeader := snapIsLeader(addr1)
	if !isLeader {
		t.Errorf("expect isLeader true get %v", isLeader)
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
