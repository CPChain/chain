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

package election

import (
	"fmt"
	"sort"
	"testing"

	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"github.com/ethereum/go-ethereum/common"
)

func TestElect(t *testing.T) {
	a := []int64{1, 2, 5, 6, 6, 7, 8, 9}
	target := float64(4)
	nearest, pos := findNearest(a, target)
	fmt.Println(nearest, pos)
	if nearest != 5 || pos != 2 {
		t.Error("findNearest error.")
	}

	var addresses [10]common.Address

	for i := 0; i < len(addresses); i++ {
		addresses[i] = common.HexToAddress("0x" + fmt.Sprintf("%040x", i))
	}

	b := rpt.RptList{
		rpt.Rpt{Address: addresses[0], Rpt: 12},
		rpt.Rpt{Address: addresses[1], Rpt: 3},
		rpt.Rpt{Address: addresses[2], Rpt: 6},
	}

	fmt.Println("before sort:")
	for i := 0; i < len(b); i++ {
		fmt.Println(b[i].Address.Hex(), b[i].Rpt)
	}

	sort.Sort(b)

	fmt.Println("after sort:")
	for i := 0; i < len(b); i++ {
		fmt.Println(b[i].Address.Hex(), b[i].Rpt)
	}

	rptx := [10]int64{100, 95, 80, 70, 60, 53, 42, 30, 10, 5}

	rpts := rpt.RptList{rpt.Rpt{Address: addresses[0], Rpt: rptx[0]}}
	for i := 1; i < len(addresses); i++ {
		rpts = append(rpts, rpt.Rpt{Address: addresses[i], Rpt: rptx[i]})
	}

	seed := int64(66)
	viewLength := 5
	signers := Elect(rpts, seed, viewLength)

	fmt.Println("commissioners:")
	for i := 0; i < len(signers); i++ {
		fmt.Println(i, signers[uint64(i)].Hex())
	}

	expectedCommittee := []common.Address{
		addresses[4],
		addresses[1],
		addresses[0],
		addresses[2],
		addresses[3],
	}
	for i := 0; i < viewLength; i++ {
		if signers[uint64(i)] != expectedCommittee[i] {
			t.Error("elect error.")
		}
	}

}
