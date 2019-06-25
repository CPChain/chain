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

package rpt

// this package collects all reputation calculation related information,
// then calculates the reputations of candidates.

import (
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	rptContract "bitbucket.org/cpchain/chain/contracts/dpor/rpt"
	"github.com/ethereum/go-ethereum/common"
)

const (
	defaultTotalSeats  = 8
	defaultLowRptSeats = 2
	defaultLowRptPct   = 50

	defaultMinimumRptValue = 1000
)

// RptService provides methods to obtain all rpt related information from block txs and contracts.
type RptService interface {
	CalcRptInfoList(addresses []common.Address, number uint64) RptList
	CalcRptInfo(address common.Address, addresses []common.Address, blockNum uint64) Rpt
	TotalSeats() (int, error)
	LowRptSeats() (int, error)
	LowRptCount(total int) int
}

// RptCollector collects rpts infos of a given candidate
type RptCollector interface {
	RptOf(addr common.Address, addrs []common.Address, num uint64) Rpt
}

// BasicCollector is the default rpt collector
type RptServiceImpl struct {
	client bind.ContractBackend

	contractAddr common.Address
	rptInstance  *rptContract.Rpt
	rptCollector RptCollector
}

// NewRptService creates a concrete RPT service instance.
func NewRptService(contractAddr common.Address, backend backend.ClientBackend) (RptService, error) {

	rptInstance, err := rptContract.NewRpt(contractAddr, backend)
	if err != nil {
		log.Error("New rpt contract 2 error")
	}

	newRptCollector := NewRptCollectorImpl6(rptInstance, backend)

	bc := &RptServiceImpl{
		client: backend,

		contractAddr: contractAddr,
		rptInstance:  rptInstance,
		rptCollector: newRptCollector,
	}
	return bc, nil
}

// TotalSeats returns total dynaimc seats
func (rs *RptServiceImpl) TotalSeats() (int, error) {
	if rs.rptInstance == nil {
		log.Error("New rpt contract 2 error")
		return defaultTotalSeats, nil
	}

	instance := rs.rptInstance
	ts, err := instance.TotalSeats(nil)
	if err != nil {
		log.Error("Get total seats error", "error", err)
		return defaultTotalSeats, err
	}

	// some restrictions to avoid some unnecessary errors
	if ts.Int64() <= 0 {
		return 0, nil
	}

	if ts.Int64() >= defaultTotalSeats {
		return defaultTotalSeats, nil
	}

	return int(ts.Int64()), nil
}

// LowRptSeats returns low rpt seats
func (rs *RptServiceImpl) LowRptSeats() (int, error) {
	if rs.rptInstance == nil {
		log.Error("New rpt contract 2 error")
		return defaultLowRptSeats, nil
	}

	instance := rs.rptInstance
	lrs, err := instance.LowRptSeats(nil)
	if err != nil {
		log.Error("Get low rpt seats error", "error", err)
		return defaultLowRptSeats, err
	}

	// some restrictions to avoid some unnecessary errors
	if lrs.Int64() <= 0 {
		return 0, nil
	}

	if lrs.Int64() >= defaultLowRptSeats {
		return defaultLowRptSeats, nil
	}

	return int(lrs.Int64()), nil
}

// LowRptPercentage returns low rpt percentage among all rpt list
func (rs *RptServiceImpl) LowRptPercentage() (int, error) {
	if rs.rptInstance == nil {
		log.Error("New rpt contract 2 error")
		return defaultLowRptPct, nil
	}

	instance := rs.rptInstance
	lrp, err := instance.LowRptPercentage(nil)
	if err != nil {
		log.Error("Get low rpt percentage error", "error", err)
		return defaultLowRptPct, err
	}

	// some restrictions to avoid some unnecessary errors
	if lrp.Int64() <= 0 {
		return 0, nil
	}

	if lrp.Int64() >= defaultLowRptPct {
		return defaultLowRptPct, nil
	}

	return int(lrp.Int64()), nil
}

// LowRptCount returns LowRptCount
func (rs *RptServiceImpl) LowRptCount(total int) int {
	pct, _ := rs.LowRptPercentage()
	return PctCount(pct, total)
}

// CalcRptInfoList returns reputation of
// the given addresses.
func (rs *RptServiceImpl) CalcRptInfoList(addresses []common.Address, number uint64) RptList {
	tstart := time.Now()

	rpts := RptList{}
	for _, address := range addresses {
		tistart := time.Now()
		rpts = append(rpts, rs.CalcRptInfo(address, addresses, number))
		log.Debug("calculate rpt for", "addr", address.Hex(), "number", number, "elapsed", common.PrettyDuration(time.Now().Sub(tistart)))
	}

	log.Debug("calculate rpt from chain backend", "number", number, "elapsed", common.PrettyDuration(time.Now().Sub(tstart)))

	return rpts
}

// CalcRptInfo return the Rpt of the candidate address
func (rs *RptServiceImpl) CalcRptInfo(address common.Address, addresses []common.Address, number uint64) Rpt {
	log.Debug("now calc rpt for with rpt method 6", "addr", address.Hex(), "number", number)
	return rs.rptCollector.RptOf(address, addresses, number)
}
