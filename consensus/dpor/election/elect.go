// Package election implements dpor's election method.
package election

import (
	"math"
	"math/rand"
	"sort"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/dpor/rpt"
)

// randRange returns a random integer between i and j.
func randRange(i, j int) int {
	if j > i {
		return i + rand.Intn(j-i)
	}
	return j + rand.Intn(i-j)
}

func getClosest(val1 float64, val2 float64, target float64, mid int) (float64, int) {
	if target-val1 <= val2-target {
		return val1, mid - 1
	}
	return val2, mid
}

// findNearest returns the value and the position when finding the nearest item
// in a slice `array' with target `target'.
func findNearest(array []float64, target float64) (float64, int) {
	n := len(array)
	if target <= array[0] {
		return array[0], 0
	}
	if target >= array[n-1] {
		return array[n-1], n - 1
	}

	// Doing binary search
	i, mid := 0, 0
	j := n

	for i < j {
		mid = (i + j) / 2

		if array[mid] == target {
			return array[mid], mid
		}

		if target < array[mid] {
			if mid > 0 && target > array[mid-1] {
				return getClosest(array[mid-1], array[mid], target, mid)
			}
			j = mid

		} else {
			if mid < n-1 && target < array[mid+1] {
				return getClosest(array[mid], array[mid+1], target, mid+1)
			}
			i = mid + 1
		}
	}
	return array[mid], mid
}

// when given a candidate's reputation dict, a random seed, and the size
// of the committee, `election' method returns an unique election result.
func elect(rpts rpt.RPTs, seed int, viewLength int) map[int]common.Address {
	sort.Sort(rpts)
	sortedRpts := rpts
	rand.Seed(int64(seed))

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
	commissioners := map[int]common.Address{0: sortedRpts[0].Address}

	for i := 0; i < viewLength; i++ {
		var srpts []float64
		for j := 0; j < len(scaledRpts); j++ {
			srpts = append(srpts, scaledRpts[j].Rpt)
		}
		_, pos := findNearest(srpts, randoms[i])

		commissioners[i] = scaledRpts[pos].Address
		scaledRpts = append(scaledRpts[:pos], scaledRpts[pos+1:]...)

	}
	return commissioners
}
