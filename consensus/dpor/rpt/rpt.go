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
	"context"
	"fmt"
	"math"
	"math/big"
	"sort"
	"strings"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"
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
	campaignContractAddr common.Address
	client               bind.ContractBackend
}

// NewCandidateService creates a concrete candidate service instance.
func NewCandidateService(backend bind.ContractBackend, contractAddr common.Address) (CandidateService, error) {
	log.Debug("candidate contract addr", "contractAddr", contractAddr.Hex())

	rs := &CandidateServiceImpl{
		client:               backend,
		campaignContractAddr: contractAddr,
	}
	return rs, nil
}

// CandidatesOf implements CandidateService
func (rs *CandidateServiceImpl) CandidatesOf(term uint64) ([]common.Address, error) {
	contractInstance, err := campaign.NewCampaign(rs.campaignContractAddr, rs.client)
	cds, err := contractInstance.CandidatesOf(nil, new(big.Int).SetUint64(term))
	if err != nil {
		return nil, err
	}
	return cds, nil
}

// RptService provides methods to obtain all rpt related information from block txs and contracts.
type RptService interface {
	CalcRptInfoList(addresses []common.Address, number uint64) RptList
	CalcRptInfo(address common.Address, number uint64) Rpt
	WindowSize() (uint64, error)
}

// BasicCollector is the default rpt collector
type RptServiceImpl struct {
	rptContract common.Address
	client      bind.ContractBackend
	rptInstance *contracts.Rpt

	rptcache *lru.ARCCache

	rptCollector RptCollector
}

// NewRptService creates a concrete RPT service instance.
func NewRptService(backend backend.ClientBackend, rptContractAddr common.Address) (RptService, error) {
	log.Debug("rptContractAddr", "contractAddr", rptContractAddr.Hex())

	rptInstance, err := contracts.NewRpt(rptContractAddr, backend)
	if err != nil {
		log.Fatal("New primitivesContract error")
	}

	cache, _ := lru.NewARC(cacheSize)

	newRptCollector := NewRptCollectorImpl(rptInstance, backend)

	bc := &RptServiceImpl{
		client:      backend,
		rptContract: rptContractAddr,
		rptInstance: rptInstance,
		rptcache:    cache,

		rptCollector: newRptCollector,
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

		if number < configs.RptCalcMethod2BlockNumber {
			rpts = append(rpts, rs.CalcRptInfo(address, number))
		} else {
			rpts = append(rpts, rs.rptCollector.RptOf(address, addresses, number))
		}

		log.Debug("calculate rpt for", "addr", address.Hex(), "number", number, "elapsed", common.PrettyDuration(time.Now().Sub(tistart)))
	}

	log.Debug("calculate rpt from chain backend", "number", number, "elapsed", common.PrettyDuration(time.Now().Sub(tstart)))

	return rpts
}

// CalcRptInfo return the Rpt of the candidate address
func (rs *RptServiceImpl) CalcRptInfo(address common.Address, blockNum uint64) Rpt {
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

func RptHash(rpthash RptItems) (hash common.Hash) {
	hasher := sha3.NewKeccak256()

	rlp.Encode(hasher, []interface{}{
		rpthash.Nodeaddress,
		rpthash.Key,
	})
	hasher.Sum(hash[:0])
	return hash
}

// RptCollector collects rpts infos of a given candidate
type RptCollector interface {
	RptOf(addr common.Address, addrs []common.Address, num uint64) Rpt
	RankValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64
	TxsValueOf(addr common.Address, num uint64, windowSize int) int64
	MaintenanceValueOf(addr common.Address, num uint64, windowSize int) int64
	UploadValueOf(addr common.Address, num uint64, windowSize int) int64
	ProxyValueOf(addr common.Address, num uint64, windowSize int) int64
}

// RptCollectorImpl implements RptCollector
type RptCollectorImpl struct {
	rptInstance  *contracts.Rpt
	chainBackend backend.ChainBackend
	balances     *balanceCache

	alpha int64
	beta  int64
	gamma int64
	psi   int64
	omega int64

	windowSize int

	currentNum uint64
	lock       sync.RWMutex
}

func NewRptCollectorImpl(rptInstance *contracts.Rpt, chainBackend backend.ChainBackend) *RptCollectorImpl {

	return &RptCollectorImpl{
		rptInstance:  rptInstance,
		chainBackend: chainBackend,
		balances:     newBalanceCache(),
		currentNum:   0,

		alpha: 50,
		beta:  15,
		gamma: 10,
		psi:   15,
		omega: 10,

		windowSize: 100,
	}
}

func (rc *RptCollectorImpl) Alpha(num uint64) int64 {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	if rc.rptInstance == nil || num == rc.currentNum {
		return rc.alpha
	}

	a, err := rc.rptInstance.Alpha(nil)
	if err == nil {
		log.Debug("using parameters from contract", "alpha", a.Int64(), "num", num)
		rc.alpha = a.Int64()
	}

	return rc.alpha
}

func (rc *RptCollectorImpl) Beta(num uint64) int64 {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	if rc.rptInstance == nil || num == rc.currentNum {
		return rc.beta
	}

	b, err := rc.rptInstance.Beta(nil)
	if err == nil {
		log.Debug("using parameters from contract", "beta", b.Int64(), "num", num)
		rc.beta = b.Int64()
	}

	return rc.beta
}

func (rc *RptCollectorImpl) Gamma(num uint64) int64 {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	if rc.rptInstance == nil || num == rc.currentNum {
		return rc.gamma
	}

	g, err := rc.rptInstance.Gamma(nil)
	if err == nil {
		log.Debug("using parameters from contract", "gamma", g.Int64(), "num", num)
		rc.gamma = g.Int64()
	}

	return rc.gamma
}

func (rc *RptCollectorImpl) Psi(num uint64) int64 {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	if rc.rptInstance == nil || num == rc.currentNum {
		return rc.psi
	}

	p, err := rc.rptInstance.Psi(nil)
	if err == nil {
		log.Debug("using parameters from contract", "psi", p.Int64(), "num", num)
		rc.psi = p.Int64()
	}

	return rc.psi
}

func (rc *RptCollectorImpl) Omega(num uint64) int64 {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	if rc.rptInstance == nil || num == rc.currentNum {
		return rc.omega
	}

	o, err := rc.rptInstance.Omega(nil)
	if err == nil {
		log.Debug("using parameters from contract", "omega", o.Int64(), "num", num)
		rc.omega = o.Int64()
	}

	return rc.omega
}

func (rc *RptCollectorImpl) WindowSize(num uint64) int {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	if rc.rptInstance == nil || num == rc.currentNum {
		return rc.windowSize
	}

	w, err := rc.rptInstance.Window(nil)
	if err == nil {
		log.Debug("using parameters from contract", "window", w.Int64(), "num", num)
		rc.windowSize = int(w.Int64())
	}

	return rc.windowSize
}

func (rc *RptCollectorImpl) coefficients(num uint64) (int64, int64, int64, int64, int64) {
	return rc.Alpha(num), rc.Beta(num), rc.Gamma(num), rc.Psi(num), rc.Omega(num)
}

func (rc *RptCollectorImpl) RptOf(addr common.Address, addrs []common.Address, num uint64) Rpt {

	windowSize := rc.WindowSize(num)
	alpha, beta, gamma, psi, omega := rc.coefficients(num)
	if num != rc.currentNum {
		rc.currentNum = num
	}

	rpt := int64(0)
	rpt = alpha*rc.RankValueOf(addr, addrs, num, windowSize) + beta*rc.TxsValueOf(addr, num, windowSize) + gamma*rc.MaintenanceValueOf(addr, num, windowSize) + psi*rc.UploadValueOf(addr, num, windowSize) + omega*rc.ProxyValueOf(addr, num, windowSize)

	if rpt <= minRptScore {
		rpt = minRptScore
	}
	return Rpt{Address: addr, Rpt: rpt}
}

// termOf returns the term of a given block number
func termOf(number uint64) uint64 {
	term := (number - 1) / (configs.ChainConfigInfo().Dpor.TermLen * configs.ChainConfigInfo().Dpor.ViewLen)
	return term
}

func offset(number uint64, windowSize int) uint64 {
	return uint64(math.Max(0., float64(int(number)-windowSize)))
}

func (rc *RptCollectorImpl) RankValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {

	rank := rc.RankInfoOf(addr, addrs, num, windowSize)

	// some simple scoring
	if rank < 2 {
		return 100
	}

	if rank < 5 {
		return 90
	}

	if rank < 15 {
		return 80
	}

	if rank < 35 {
		return 70
	}

	if rank < 60 {
		return 60
	}

	if rank < 80 {
		return 40
	}

	return 20
}

func (rc *RptCollectorImpl) TxsValueOf(addr common.Address, num uint64, windowSize int) int64 {
	count := rc.TxsInfoOf(addr, num, windowSize)

	if count > 100 {
		return 100
	}

	return count
}

func (rc *RptCollectorImpl) MaintenanceValueOf(addr common.Address, num uint64, windowSize int) int64 {
	return rc.MaintenanceInfoOf(addr, num, windowSize)
}

func (rc *RptCollectorImpl) UploadValueOf(addr common.Address, num uint64, windowSize int) int64 {
	return rc.UploadInfoOf(addr, num, windowSize)
}

func (rc *RptCollectorImpl) ProxyValueOf(addr common.Address, num uint64, windowSize int) int64 {
	return rc.ProxyInfoOf(addr, num, windowSize)
}

type balanceCache struct {
	cache *lru.ARCCache
}

func newBalanceCache() *balanceCache {
	cache, _ := lru.NewARC(10)
	return &balanceCache{
		cache: cache,
	}
}

func (bc *balanceCache) getBalances(num uint64) ([]float64, bool) {
	if bal, ok := bc.cache.Get(num); ok {
		if balances, ok := bal.([]float64); ok {
			return balances, true
		}
	}
	return []float64{}, false
}

func (bc *balanceCache) addBalance(num uint64, sortedBalances []float64) {
	bc.cache.Add(num, sortedBalances)
}

func (rc *RptCollectorImpl) RankInfoOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	tstart := time.Now()

	var rank int64
	myBal, err := rc.chainBackend.BalanceAt(context.Background(), addr, big.NewInt(int64(num)))
	if err != nil {
		return defaultRank
	}
	myBalance := myBal.Uint64()

	balances, ok := rc.balances.getBalances(num)
	if !ok {
		for _, candidate := range addrs {
			balance, err := rc.chainBackend.BalanceAt(context.Background(), candidate, big.NewInt(int64(num)))
			if err != nil {
				return defaultRank
			}

			if candidate == addr {
				myBalance = balance.Uint64()
			}

			balances = append(balances, float64(balance.Uint64()))
		}
		sort.Sort(sort.Reverse(sort.Float64Slice(balances)))
		rc.balances.addBalance(num, balances)
	}

	// sort and get the rank
	index := sort.SearchFloat64s(balances, float64(myBalance))
	rank = int64(float64(index) / float64(len(addrs)) * 100)

	log.Debug("now calculating rpt", "Rank", "new", "num", num, "addr", addr.Hex(), "elapsed", common.PrettyDuration(time.Now().Sub(tstart)))
	return rank
}

func (rc *RptCollectorImpl) TxsInfoOf(addr common.Address, num uint64, windowSize int) int64 {
	tstart := time.Now()
	txsCount := int64(0)

	nonce, err := rc.chainBackend.NonceAt(context.Background(), addr, big.NewInt(int64(num)))
	if err != nil {
		return txsCount
	}

	nonce0, err := rc.chainBackend.NonceAt(context.Background(), addr, big.NewInt(int64(offset(num, windowSize))))
	if err != nil {
		return txsCount
	}

	log.Debug("now calculating rpt", "Txs", "new", "num", num, "addr", addr.Hex(), "elapsed", common.PrettyDuration(time.Now().Sub(tstart)))
	return int64(nonce - nonce0)
}

func (rc *RptCollectorImpl) MaintenanceInfoOf(addr common.Address, num uint64, windowSize int) int64 {
	tstart := time.Now()

	mtn := int64(0)
	for i := offset(num, windowSize); i < num; i++ {
		header, err := rc.chainBackend.HeaderByNumber(context.Background(), big.NewInt(int64(num)))
		if err != nil {
			continue
		}

		if header.Coinbase == addr {
			mtn += 100
			continue
		}

		for _, ad := range header.Dpor.Proposers {
			if addr == ad {
				mtn += 80
				break
			}
		}

		mtn += 60
	}

	log.Debug("now calculating rpt", "Maintenance", "new", "num", num, "addr", addr.Hex(), "elapsed", common.PrettyDuration(time.Now().Sub(tstart)))
	return mtn
}

func (rc *RptCollectorImpl) UploadInfoOf(addr common.Address, num uint64, windowSize int) int64 {
	log.Debug("now calculating rpt", "UploadInfo", "new", "num", num, "addr", addr.Hex())

	return 0
}

func (rc *RptCollectorImpl) ProxyInfoOf(addr common.Address, num uint64, windowSize int) int64 {
	log.Debug("now calculating rpt", "ProxyInfo", "new", "num", num, "addr", addr.Hex())

	return 0
}
