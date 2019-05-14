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
	campaign "bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"
	campaign2 "bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign2"
	campaign3 "bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign3"
	contracts "bitbucket.org/cpchain/chain/contracts/dpor/contracts/rpt"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/rlp"
	lru "github.com/hashicorp/golang-lru"
)

const (
	defaultRank = 100 // 100 represent give the address a default rank
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

func (bc *rptDataCache) getCache(num uint64) ([]float64, bool) {
	if bal, ok := bc.cache.Get(num); ok {
		if data, ok := bal.([]float64); ok {
			return data, true
		}
	}
	return []float64{}, false
}

func (bc *rptDataCache) addCache(num uint64, sortedCache []float64) {
	bc.cache.Add(num, sortedCache)
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
		items[i] = fmt.Sprintf("[%s, %d]", v.Address.Hex(), v.Rpt)
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
			return nil, err
		}

		// candidates from old campaign contract
		cds, err := contractInstance.CandidatesOf(nil, new(big.Int).SetUint64(term))
		if err != nil {
			return nil, err
		}

		log.Debug("now read candidates from old campaign contract", "len", len(cds), "contract addr", campaignAddr.Hex())

		return cds, nil
	}

	if term < backend.TermOf(configs.Campaign3BlockNumber) {

		// new campaign contract address
		campaignAddr := configs.ChainConfigInfo().Dpor.Contracts[configs.ContractCampaign2]

		// new campaign contract instance
		contractInstance, err := campaign2.NewCampaign(campaignAddr, rs.client)
		if err != nil {
			return nil, err
		}

		// candidates from new campaign contract
		cds, err := contractInstance.CandidatesOf(nil, new(big.Int).SetUint64(term))
		if err != nil {
			return nil, err
		}

		log.Debug("now read candidates from new campaign contract", "len", len(cds), "contract addr", campaignAddr.Hex())
		return cds, nil
	}

	// new campaign contract address
	campaignAddr := configs.ChainConfigInfo().Dpor.Contracts[configs.ContractCampaign3]

	// new campaign contract instance
	contractInstance, err := campaign3.NewCampaign(campaignAddr, rs.client)
	if err != nil {
		return nil, err
	}

	// candidates from new campaign contract
	cds, err := contractInstance.CandidatesOf(nil, new(big.Int).SetUint64(term))
	if err != nil {
		return nil, err
	}

	log.Debug("now read candidates from new campaign contract", "len", len(cds), "contract addr", campaignAddr.Hex())
	return cds, nil
}

// RptService provides methods to obtain all rpt related information from block txs and contracts.
type RptService interface {
	CalcRptInfoList(addresses []common.Address, number uint64) RptList
	CalcRptInfo(address common.Address, addresses []common.Address, blockNum uint64) Rpt
	WindowSize() (uint64, error)
}

// RptCollector collects rpts infos of a given candidate
type RptCollector interface {
	RptOf(addr common.Address, addrs []common.Address, num uint64) Rpt
}

// BasicCollector is the default rpt collector
type RptServiceImpl struct {
	rptContract common.Address
	client      bind.ContractBackend
	rptInstance *contracts.Rpt

	rptcache *lru.ARCCache

	rptCollector2 RptCollector
	rptCollector3 RptCollector
	rptCollector4 RptCollector
	rptCollector5 RptCollector
}

// NewRptService creates a concrete RPT service instance.
func NewRptService(backend backend.ClientBackend, rptContractAddr common.Address) (RptService, error) {
	log.Debug("rptContractAddr", "contractAddr", rptContractAddr.Hex())

	rptInstance, err := contracts.NewRpt(rptContractAddr, backend)
	if err != nil {
		log.Fatal("New primitivesContract error")
	}

	cache, _ := lru.NewARC(cacheSize)

	newRptCollector2 := NewRptCollectorImpl2(rptInstance, backend)
	newRptCollector3 := NewRptCollectorImpl3(rptInstance, backend)
	newRptCollector4 := NewRptCollectorImpl4(rptInstance, backend)
	newRptCollector5 := NewRptCollectorImpl5(rptInstance, backend)

	bc := &RptServiceImpl{
		client:      backend,
		rptContract: rptContractAddr,
		rptInstance: rptInstance,
		rptcache:    cache,

		rptCollector2: newRptCollector2,
		rptCollector3: newRptCollector3,
		rptCollector4: newRptCollector4,
		rptCollector5: newRptCollector5,
	}
	return bc, nil
}

// WindowSize reads windowsize from rpt contract
func (rs *RptServiceImpl) WindowSize() (uint64, error) {
	if rs.rptInstance == nil {
		log.Fatal("New primitivesContract error")
	}

	instance := rs.rptInstance
	windowSize, err := instance.Window(nil)
	if err != nil {
		log.Error("Get windowSize error", "error", err)
		return 0, err
	}
	return windowSize.Uint64(), nil
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

	log.Debug("now calc rpt for with rpt method 5", "addr", address.Hex(), "number", number)
	return rs.rptCollector5.RptOf(address, addresses, number)
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

				log.Error("GetRpt error", "tryIndex", tryIndex, "error", err, "address", address.Hex(), "rs.rptContract", rs.rptContract.Hex(), "i", i, "blockNum", blockNum, "windowSize", windowSize, "blockInWindow", blockInWindow, "hash", hash.Hex())
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
