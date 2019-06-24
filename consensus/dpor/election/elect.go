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
	"math/rand"
	"sort"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"github.com/ethereum/go-ethereum/common"
)

// Elect simplifies the election method
//
// In election, a certain number of candidates (referred as *seats*) are elected to be proposer
// according to their RPT value.
// We have two principles to design the election:
//
// An RNode with higher RPT has higher chance to be elected;
// Each term of proposers has a certain number of representatives from RNodes with low RPT.
//
// Thus, the main ideas of election process are:
//
// Candidates are divided into two partitions, high-RPT RNodes and low-RPT RNodes;
// Either partition has a number of available seats;
// The probability mass for each node being elected is proportional to its RPT in its corresponding partition.
//
// rpts: the reputation list of RNodes
// seed: a seed to generate a series of random numbers to select RNodes
// totalSeats: total seats of the election result
// lowRptCount: the number of low Rpt RNodes among the total RNodes
// lowRptSeats: the number of seats for low Rpt RNodes in the Proposer Committee
func Elect(rpts rpt.RptList, seed int64, totalSeats int, lowRptCount int, lowRptSeats int) []common.Address {
	if lowRptCount > rpts.Len() || lowRptSeats > totalSeats || totalSeats > rpts.Len() || lowRptCount < lowRptSeats {
		return []common.Address{}
	}

	log.Debug("elect parameters", "seed", seed, "total seats", totalSeats, "lowRptCount", lowRptCount, "lowRptSeats", lowRptSeats)

	sort.Sort(rpts)

	lowRpts := rpts[:lowRptCount]
	highRpts := rpts[lowRptCount:]

	randSource := rand.NewSource(seed)
	myRand := rand.New(randSource)

	log.Debug("random select by rpt parameters", "lowRptSeats", lowRptSeats, "highRptSeats", totalSeats-lowRptSeats)

	lowElected := randomSelectByRpt(lowRpts, myRand, lowRptSeats)
	highElected := randomSelectByRpt(highRpts, myRand, totalSeats-lowRptSeats)

	return append(lowElected, highElected...)
}

// randomSelectByRpt
// uniform random selection from rptPartition
// the mass probability for each node being elected is proportional to its RPT
// the function select l random addresses
// and return them as result
func randomSelectByRpt(rpts rpt.RptList, myRand *rand.Rand, seats int) (result []common.Address) {
	// each element in rptPartition is referred as rpt
	// then we sum all rpt values, as sumRpt
	// random select l addresses according to its rpt/sumRpt
	// return these l addresses
	sort.Sort(rpts)

	log.Debug("seats", "seats", seats)

	sums, sum := sumOfFirstN(rpts)
	selected := make(map[int]struct{})

	log.Debug("sums and sum", "sums", sums, "sum", sum)

	for seats > 0 {
		log.Debug("seats in for loop", "seats", seats)

		randI := myRand.Int63n(sum)
		resultIdx := findHit(randI, sums)

		log.Debug("randI", "randI", randI, "result idx", resultIdx, "sum", sum, "sums", sums, "result", result)

		// if already selected, continue
		if _, already := selected[resultIdx]; already {
			continue
		}

		// not selected yet, append it!
		selected[resultIdx] = struct{}{}
		result = append(result, rpts[resultIdx].Address)

		seats--

	}
	return result
}

func findHit(hit int64, hitSums []int64) int {
	for idx, x := range hitSums {
		log.Debug("find hit", "hit", hit, "idx", idx, "x", x, "hit sums", hitSums)
		if hit <= x {
			return idx
		}
	}
	return len(hitSums) - 1
}

func sumOfFirstN(rpts rpt.RptList) (sums []int64, sum int64) {
	sum = 0
	for _, rpt := range rpts {
		sum += rpt.Rpt
		sums = append(sums, sum)
	}
	return
}
