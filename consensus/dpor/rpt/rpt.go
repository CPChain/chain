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
	"fmt"
	"math"
	"math/big"
	"strings"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	campaign "bitbucket.org/cpchain/chain/contracts/dpor/campaign"
	campaign2 "bitbucket.org/cpchain/chain/contracts/dpor/campaign2"
	campaign3 "bitbucket.org/cpchain/chain/contracts/dpor/campaign3"
	campaign4 "bitbucket.org/cpchain/chain/contracts/dpor/campaign4"
	rptContract "bitbucket.org/cpchain/chain/contracts/dpor/rpt"
	rptContract2 "bitbucket.org/cpchain/chain/contracts/dpor/rpt2"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/rlp"
	lru "github.com/hashicorp/golang-lru"
)

const (
	defaultRank = 100 // 100 represent give the address a default rank
)

const (
	defaultWindowSize  = 4
	defaultTotalSeats  = 8
	defaultLowRptSeats = 2
	defaultLowRptPct   = 50
)

var (
	extraVanity = 32 // Fixed number of extra-data prefix bytes reserved for signer vanity
	extraSeal   = 65 // Fixed number of extra-data suffix bytes reserved for signer seal

	maxRetryGetRpt = 3 // Max times Get Rpt
)

const (
	cacheSize = 1024
	// 16 is the min rpt score
	minRptScore = 16
)

// termOf returns the term of a given block number
func termOf(number uint64) uint64 {
	term := (number - 1) / (configs.ChainConfigInfo().Dpor.TermLen * configs.ChainConfigInfo().Dpor.ViewLen)
	return term
}

func offset(number uint64, windowSize int) uint64 {
	return uint64(math.Max(0., float64(int(number)-windowSize)))
}

func RptHash(rpthash RptItems) (hash common.Hash) {
	hasher := sha3.NewKeccak256()

	rlp.Encode(hasher, []interface{}{
		rpthash.Nodeaddress,
		rpthash.Key,
	})
	hasher.Sum(hash[:0])
	return hash
}

// TODO: @liuq use hash of addrs and block number as key,
// not just block number like not
type rptDataCache struct {
	cache *lru.ARCCache
}

func newRptDataCache() *rptDataCache {
	cache, _ := lru.NewARC(10)
	return &rptDataCache{
		cache: cache,
	}
}

func (bc *rptDataCache) getCache(key interface{}) ([]float64, bool) {
	if bal, ok := bc.cache.Get(key); ok {
		if data, ok := bal.([]float64); ok {
			return data, true
		}
	}
	return []float64{}, false
}

func (bc *rptDataCache) addCache(key interface{}, sortedCache []float64) {
	bc.cache.Add(key, sortedCache)
}

// Rpt defines the name and reputation pair.
type Rpt struct {
	Address common.Address
	Rpt     int64
}

type RptItems struct {
	Nodeaddress common.Address
	Key         uint64
}

// RptList is an array of Rpt.
type RptList []Rpt

func (r *RptList) FormatString() string {
	items := make([]string, len(*r))
	for i, v := range *r {
		items[i] = fmt.Sprintf("[addr: %s, rpt: #%d]", v.Address.Hex(), v.Rpt)
	}
	return strings.Join(items, ",")
}

// This is used for sorting.
func (a RptList) Len() int      { return len(a) }
func (a RptList) Swap(i, j int) { a[i], a[j] = a[j], a[i] }
func (a RptList) Less(i, j int) bool {
	if a[i].Rpt < a[j].Rpt {
		return true
	} else if a[i].Rpt > a[j].Rpt {
		return false
	} else {
		if a[i].Address.Big().Cmp(a[j].Address.Big()) < 0 {
			return true
		}
		return false
	}
}

// CandidateService provides methods to obtain all candidates from campaign contract
type CandidateService interface {
	CandidatesOf(term uint64) ([]common.Address, error)
}

// CandidateServiceImpl is the default candidate list collector
type CandidateServiceImpl struct {
	client bind.ContractBackend
}

// NewCandidateService creates a concrete candidate service instance.
func NewCandidateService(backend bind.ContractBackend) (CandidateService, error) {

	rs := &CandidateServiceImpl{
		client: backend,
	}
	return rs, nil
}

// CandidatesOf implements CandidateService
func (rs *CandidateServiceImpl) CandidatesOf(term uint64) ([]common.Address, error) {

	if term < backend.TermOf(configs.Campaign2BlockNumber) {
		// old campaign contract address
		campaignAddr := configs.ChainConfigInfo().Dpor.Contracts[configs.ContractCampaign]

		// old campaign contract instance
		contractInstance, err := campaign.NewCampaign(campaignAddr, rs.client)
		if err != nil {
			log.Debug("error when create campaign 1 instance", "err", err)
			return nil, err
		}

		// candidates from old campaign contract
		cds, err := contractInstance.CandidatesOf(nil, new(big.Int).SetUint64(term))
		if err != nil {
			log.Debug("error when read candidates from campaign 1", "err", err)
			return nil, err
		}

		log.Debug("now read candidates from campaign contract 1", "len", len(cds), "contract addr", campaignAddr.Hex())

		return cds, nil
	}

	if term < backend.TermOf(configs.Campaign3BlockNumber) {

		// new campaign contract address
		campaignAddr := configs.ChainConfigInfo().Dpor.Contracts[configs.ContractCampaign2]

		// new campaign contract instance
		contractInstance, err := campaign2.NewCampaign(campaignAddr, rs.client)
		if err != nil {
			log.Debug("error when create campaign 2 instance", "err", err)
			return nil, err
		}

		// candidates from new campaign contract
		cds, err := contractInstance.CandidatesOf(nil, new(big.Int).SetUint64(term))
		if err != nil {
			log.Debug("error when read candidates from campaign 2", "err", err)
			return nil, err
		}

		log.Debug("now read candidates from campaign contract 2", "len", len(cds), "contract addr", campaignAddr.Hex())
		return cds, nil
	}

	if term < backend.TermOf(configs.Campaign4BlockNumber) {

		// new campaign contract address
		campaignAddr := configs.ChainConfigInfo().Dpor.Contracts[configs.ContractCampaign3]

		// new campaign contract instance
		contractInstance, err := campaign3.NewCampaign(campaignAddr, rs.client)
		if err != nil {
			log.Debug("error when create campaign 3 instance", "err", err)
			return nil, err
		}

		// candidates from new campaign contract
		cds, err := contractInstance.CandidatesOf(nil, new(big.Int).SetUint64(term))
		if err != nil {
			log.Debug("error when read candidates from campaign 3", "err", err)
			return nil, err
		}

		log.Debug("now read candidates from campaign contract 3", "len", len(cds), "contract addr", campaignAddr.Hex())
		return cds, nil
	}

	// new campaign contract address
	campaignAddr := configs.ChainConfigInfo().Dpor.Contracts[configs.ContractCampaign4]

	// new campaign contract instance
	contractInstance, err := campaign4.NewCampaign(campaignAddr, rs.client)
	if err != nil {
		log.Debug("error when create campaign 4 instance", "err", err)
		return nil, err
	}

	// candidates from new campaign contract
	cds, err := contractInstance.CandidatesOf(nil, new(big.Int).SetUint64(term))
	if err != nil {
		log.Debug("error when read candidates from campaign 4", "err", err)
		return nil, err
	}

	log.Debug("now read candidates from campaign contract 4", "len", len(cds), "contract addr", campaignAddr.Hex())
	return cds, nil
}

// RptService provides methods to obtain all rpt related information from block txs and contracts.
type RptService interface {
	CalcRptInfoList(addresses []common.Address, number uint64) RptList
	CalcRptInfo(address common.Address, addresses []common.Address, blockNum uint64) Rpt
	TotalSeats() (int, error)
	LowRptSeats() (int, error)
	LowRptCounts(total int) int
}

// RptCollector collects rpts infos of a given candidate
type RptCollector interface {
	RptOf(addr common.Address, addrs []common.Address, num uint64) Rpt
}

// BasicCollector is the default rpt collector
type RptServiceImpl struct {
	client bind.ContractBackend

	rptContractAddr  common.Address
	rptContractAddr2 common.Address

	rptInstance  *rptContract.Rpt
	rptInstance2 *rptContract2.Rpt

	rptcache *lru.ARCCache

	rptCollector2 RptCollector
	rptCollector3 RptCollector
	rptCollector4 RptCollector
	rptCollector5 RptCollector
	rptCollector6 RptCollector
}

// NewRptService creates a concrete RPT service instance.
func NewRptService(backend backend.ClientBackend, rptContractAddr common.Address, rptContractAddr2 common.Address) (RptService, error) {
	log.Debug("rptContractAddr", "contractAddr", rptContractAddr.Hex())

	rptInstance, err := rptContract.NewRpt(rptContractAddr, backend)
	if err != nil {
		log.Error("New rpt contract error")
	}

	rptInstance2, err := rptContract2.NewRpt(rptContractAddr2, backend)
	if err != nil {
		log.Error("New rpt contract 2 error")
	}

	cache, _ := lru.NewARC(cacheSize)

	newRptCollector2 := NewRptCollectorImpl2(rptInstance, backend)
	newRptCollector3 := NewRptCollectorImpl3(rptInstance, backend)
	newRptCollector4 := NewRptCollectorImpl4(rptInstance, backend)
	newRptCollector5 := NewRptCollectorImpl5(rptInstance, backend)
	newRptCollector6 := NewRptCollectorImpl6(rptInstance2, backend)

	bc := &RptServiceImpl{
		client:   backend,
		rptcache: cache,

		rptInstance:  rptInstance,
		rptInstance2: rptInstance2,

		rptContractAddr:  rptContractAddr,
		rptContractAddr2: rptContractAddr2,

		rptCollector2: newRptCollector2,
		rptCollector3: newRptCollector3,
		rptCollector4: newRptCollector4,
		rptCollector5: newRptCollector5,
		rptCollector6: newRptCollector6,
	}
	return bc, nil
}

// TotalSeats returns total dynaimc seats
func (rs *RptServiceImpl) TotalSeats() (int, error) {
	if rs.rptInstance2 == nil {
		log.Error("New rpt contract 2 error")
		return defaultTotalSeats, nil
	}

	instance := rs.rptInstance2
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
	if rs.rptInstance2 == nil {
		log.Error("New rpt contract 2 error")
		return defaultLowRptSeats, nil
	}

	instance := rs.rptInstance2
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
	if rs.rptInstance2 == nil {
		log.Error("New rpt contract 2 error")
		return defaultLowRptPct, nil
	}

	instance := rs.rptInstance2
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

// LowRptCounts returns LowRptCounts
func (rs *RptServiceImpl) LowRptCounts(total int) int {
	pct, _ := rs.LowRptPercentage()
	return PctCount(pct, total)
}

// PctCount calcs #pct percentage of #total
func PctCount(pct int, total int) int {
	return int(float64(pct) * 0.01 * float64(total))
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
	if number < configs.RptCalcMethod2BlockNumber {
		log.Debug("now calc rpt for with old rpt method", "addr", address.Hex(), "number", number)
		return rs.calcRptInfo(address, number)
	}

	if number < configs.RptCalcMethod3BlockNumber {
		log.Debug("now calc rpt for with rpt method 2", "addr", address.Hex(), "number", number)
		return rs.rptCollector2.RptOf(address, addresses, number)
	}

	if number < configs.RptCalcMethod4BlockNumber {
		log.Debug("now calc rpt for with rpt method 3", "addr", address.Hex(), "number", number)
		return rs.rptCollector3.RptOf(address, addresses, number)
	}

	if number < configs.RptCalcMethod5BlockNumber {
		log.Debug("now calc rpt for with rpt method 4", "addr", address.Hex(), "number", number)
		return rs.rptCollector4.RptOf(address, addresses, number)
	}

	if number < configs.RptCalcMethod6BlockNumber {
		log.Debug("now calc rpt for with rpt method 5", "addr", address.Hex(), "number", number)
		return rs.rptCollector5.RptOf(address, addresses, number)
	}

	log.Debug("now calc rpt for with rpt method 6", "addr", address.Hex(), "number", number)
	return rs.rptCollector6.RptOf(address, addresses, number)
}

func (rs *RptServiceImpl) calcRptInfo(address common.Address, blockNum uint64) Rpt {
	log.Debug("now calculating rpt", "CalcRptInfo", "old", "num", blockNum, "addr", address.Hex())

	if rs.rptInstance == nil {
		log.Fatal("New primitivesContract error")
	}

	instance := rs.rptInstance

	rpt := int64(0)
	windowSize, err := instance.Window(nil)
	if err != nil {
		log.Error("Get windowSize error", "error", err)
		return Rpt{Address: address, Rpt: minRptScore}
	}
	blockInWindow := int64(blockNum) - windowSize.Int64()
	log.Debug("blockInWindow", "blockInWindow", blockInWindow, "blockNum", blockNum)
	for i := int64(blockNum); i >= 0 && i >= blockInWindow; i-- {
		hash := RptHash(RptItems{Nodeaddress: address, Key: uint64(i)})
		rc, exists := rs.rptcache.Get(hash)
		if !exists {
			// try get rpt ${maxRetryGetRpt} times
			for tryIndex := 0; tryIndex <= maxRetryGetRpt; tryIndex++ {
				rptInfo, err := instance.GetRpt(nil, address, new(big.Int).SetInt64(i))
				if err == nil {
					log.Debug("GetRpt ok", "tryIndex", tryIndex, "hash", hash.Hex(), "blockNum", blockNum, "i", i)
					rs.rptcache.Add(hash, Rpt{Address: address, Rpt: rptInfo.Int64()})
					rpt += rptInfo.Int64()
					break
				}

				log.Error("GetRpt error", "tryIndex", tryIndex, "error", err, "address", address.Hex(), "rs.rptContract", rs.rptContractAddr.Hex(), "i", i, "blockNum", blockNum, "windowSize", windowSize, "blockInWindow", blockInWindow, "hash", hash.Hex())
				if tryIndex < maxRetryGetRpt {
					// retry
					continue
				}
				// get rpt failed
				log.Error("GetRpt failed", "tryIndex", tryIndex, "hash", hash.Hex(), "blockNum", blockNum, "i", i)
				return Rpt{Address: address, Rpt: minRptScore}
			}

		} else {
			if value, ok := rc.(Rpt); ok {
				rpt += value.Rpt
			}
		}
	}

	if rpt <= minRptScore {
		rpt = minRptScore
	}
	return Rpt{Address: address, Rpt: rpt}
}
