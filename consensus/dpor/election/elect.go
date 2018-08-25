// Package election implements dpor's election method.
package election

import (
	"math"
	"math/rand"
	"sort"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/dpor/rpt"
)

// randRange returns a random integer between [ min(i,j), max(i,j) )
// NB, the rhs is open.
func randRange(i, j int) int {
	if j > i {
		return i + rand.Intn(j-i)
	}
	return j + rand.Intn(i-j)
}

func findNearest(array []float64, target float64) (float64, int) {
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
func Elect(rpts rpt.RPTs, seed int64, viewLength int) []common.Address {
	sort.Sort(rpts)
	sortedRpts := rpts
	rand.Seed(seed)

	upper := 10
	lower := 0
	step := (upper - lower) / viewLength

	var randoms []float64

	for i := 0; i < viewLength; i++ {
		rnd := randRange(i*step, (i+1)*step)
		randoms = append(randoms, math.Log2(float64(1.0+rnd)))
	}

	scale := sortedRpts[len(sortedRpts)-1].Rpt / math.Log2(float64(1+upper))
	scaledRpts := sortedRpts
	for i := 0; i < len(sortedRpts); i++ {
		scaledRpts[i].Rpt /= scale
	}

	signers := make([]common.Address, viewLength)

	for i := 0; i < viewLength; i++ {
		var srpts []float64
		for j := 0; j < len(scaledRpts); j++ {
			srpts = append(srpts, scaledRpts[j].Rpt)
		}
		_, pos := findNearest(srpts, randoms[i])

		signers[i] = scaledRpts[pos].Address
		scaledRpts = append(scaledRpts[:pos], scaledRpts[pos+1:]...)

	}
	return signers
}
