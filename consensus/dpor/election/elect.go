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

// Package election implements dpor's election method.
package election

import (
	"math"
	"math/rand"
	"sort"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"github.com/ethereum/go-ethereum/common"
)

// randRange returns a random integer between [ min(i,j), max(i,j) )
// NB, the rhs is open.
func randRange(i, j int, myrand *rand.Rand) int {
	if j > i {
		return i + myrand.Intn(j-i)
	}
	return j + myrand.Intn(i-j)
}

func findNearest(array []int64, target int64) (int64, int) {
	if len(array) == 0 {
		panic("array length must be nonzero.")
	}

	lo, hi := 0, len(array)-1

	// invariant: the nearest number is always within [lo,hi]
	for lo+1 < hi {
		mid := lo + (hi-lo)/2
		if array[mid] >= target {
			hi = mid
		} else {
			lo = mid
		}
	}

	if array[lo] >= target {
		return array[lo], lo
	} else if array[hi] <= target {
		return array[hi], hi
	} else {
		// ok.  we check the gap
		if target-array[lo] <= array[hi]-target {
			return array[lo], lo
		}
		return array[hi], hi
	}
}

// Elect returns election result of the given rpt list of candidates,
// seed and viewLength.
func Elect(rpts rpt.RptList, seed int64, viewLength int) []common.Address {
	sort.Sort(rpts)
	sortedRpts := rpts

	log.Info("lenth of rpts", "len", len(rpts))
	for _, r := range rpts {
		log.Info("rptlist", "addr", r.Address, "rpt", r.Rpt)
	}

	randSource := rand.NewSource(seed)
	myRand := rand.New(randSource)

	upper := 10
	lower := 0
	step := (upper - lower) / viewLength

	var randoms []int64

	for i := 0; i < viewLength; i++ {
		rnd := randRange(i*step, (i+1)*step, myRand)
		randoms = append(randoms, int64(math.Log2(float64(1.0+rnd))))
	}

	scale := sortedRpts[len(sortedRpts)-1].Rpt / int64(math.Log2(float64(1+upper)))
	scaledRpts := sortedRpts
	for i := 0; i < len(sortedRpts); i++ {
		scaledRpts[i].Rpt /= scale
	}

	signers := make([]common.Address, viewLength)

	for i := 0; i < viewLength; i++ {
		var srpts []int64
		for j := 0; j < len(scaledRpts); j++ {
			srpts = append(srpts, scaledRpts[j].Rpt)
		}
		_, pos := findNearest(srpts, randoms[i])

		signers[i] = scaledRpts[pos].Address
		scaledRpts = append(scaledRpts[:pos], scaledRpts[pos+1:]...)

	}
	return signers
}
