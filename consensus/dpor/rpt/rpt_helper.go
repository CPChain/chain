package rpt

import (
	"context"
	"fmt"
	"math"
	"math/big"
	"sort"
	"strings"
	"sync"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/rlp"
	lru "github.com/hashicorp/golang-lru"
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
		items[i] = fmt.Sprintf("[addr: %s, rpt: #%d]", v.Address.Hex(), v.Rpt)
	}
	return strings.Join(items, ",")
}

func (a RptList) Addrs() (addrs []common.Address) {
	for _, rptItem := range a {
		addrs = append(addrs, rptItem.Address)
	}
	return addrs
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

// termOf returns the term of a given block number
func termOf(number uint64) uint64 {
	term := (number - 1) / (configs.ChainConfigInfo().Dpor.TermLen * configs.ChainConfigInfo().Dpor.ViewLen)
	return term
}

func offset(number uint64, windowSize int) uint64 {
	return uint64(math.Max(0., float64(int(number)-windowSize)))
}

// getRank return the rank of the given item among the array
// the array is in decreasing order
func getRank(item float64, array sort.Float64Slice) int64 {
	len := len(array)
	index := searchIndex(item, array)
	rank := int64((1 - float64(index)/float64(len)) * 100)
	log.Debug("array", "array", array, "rank", rank, "index", index, "len", len)
	return rank
}

// sortAndReverse returns an decreasing order of the given array
func sortAndReverse(array []float64) sort.Float64Slice {
	sort.Sort(sort.Reverse(sort.Float64Slice(array)))
	return array
}

// searchIndex return the index of an item in an array
func searchIndex(item float64, array []float64) int64 {
	for i, x := range array {
		if x == item {
			return int64(i)
		}
	}
	return int64(len(array))
}

type rptCalcItemKey struct {
	num   uint64
	addrs common.Hash
}

func newRptDataCacheKey(num uint64, addrs []common.Address) rptCalcItemKey {
	hasher := sha3.NewKeccak256()
	var hash common.Hash

	rlp.Encode(hasher, func(addrs []common.Address) (result []interface{}) {
		for _, addr := range addrs {
			result = append(result, addr)
		}
		return
	}(addrs))

	hasher.Sum(hash[:0])

	return rptCalcItemKey{
		num:   num,
		addrs: hash,
	}
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

// PctCount calcs #pct percentage of #total
func PctCount(pct int, total int) int {
	return int(float64(pct) * 0.01 * float64(total))
}

// impeachHistory records impeach history of reputation nodes
type impeachHistory interface {
	addHistory(addr common.Address, num uint64, isImpeach bool) error
	addHistories(outset, current uint64, chainBackend backend.ChainBackend)
	countHistory(addr common.Address) int
	currentNumber() uint64
}

// record is a slice to record impeached block number of an reputation node address
type record struct {
	r []uint64
}

func newRecord() *record {
	return &record{
		r: []uint64{},
	}
}

// clean cleans all those records(impeached block number) less than or equal to outset
func (r *record) clean(outset uint64) {
	log.Debug("length of record before clean", "len", len(r.r), "outset", outset)
	defer log.Debug("length of record after clean", "len", len(r.r), "outset", outset)

	l := len(r.r)
	if l == 0 {
		return
	}

	// if the last item is less than or equal to outset, clean all
	if r.r[l-1] <= outset {
		r.r = []uint64{}
	}

	// find the index of the first item larger than outset
	cutIdx := 0
	for i, x := range r.r {
		if x > outset {
			cutIdx = i
			break
		}
	}

	// cut those previous items
	if cutIdx != 0 {
		r.r = append([]uint64{}, r.r[cutIdx:]...)
	}
}

// countAfter returns count of impeach numbers larger than the outset
func (r *record) countAfter(outset uint64) int {
	r.clean(outset)
	return len(r.r)
}

func (r *record) push(item uint64) {
	log.Debug("pushed item to impeach history record", "num", item)

	r.r = append(r.r, item)
}

type impeachHistoryImpl struct {
	records map[common.Address]*record
	outset  uint64
	latest  uint64
	lock    sync.RWMutex
}

// outsetOf returns #(current-window) or 0 if negative.
func outsetOf(current uint64) uint64 {
	if current > impeachPunishmentWindowSize {
		return current - impeachPunishmentWindowSize
	}
	return 0
}

// newImpeachHistoryImpl creates an impeach history records, used for punishing impeached proposers
// by decrease their rpt value
func newImpeachHistoryImpl(current uint64, chainBackend backend.ChainBackend) impeachHistory {
	outset := outsetOf(current)
	ih := &impeachHistoryImpl{
		outset:  outset,
		latest:  outset,
		records: make(map[common.Address]*record),
	}

	// update those old impeach states
	ih.addHistories(outset, current, chainBackend)
	return ih
}

// addHistories updates a batch of histories, a history record means a block impeach status(impeached or not).
func (ih *impeachHistoryImpl) addHistories(outset uint64, current uint64, chainBackend backend.ChainBackend) {

	// range of impeach status is (outset, current], max length of this range is window size
	for numIter := outset + 1; numIter <= current; numIter++ {

		log.Debug("updating impeach history", "num", numIter, "outset", outset, "current", current)

		// retrieve the block header by the iter number
		header, err := chainBackend.HeaderByNumber(context.Background(), new(big.Int).SetUint64(numIter))
		if header == nil || err != nil {
			log.Fatal("failed to retrieve header from local chain", "err", err)
		}

		var (
			isImpeach = false
			addr      = header.Coinbase
		)

		// if the block is impeached, get the impeached proposer
		if header.Impeachment() {
			isImpeach = true
			addr, err = backend.ImpeachedProposer(header)
			if err != nil {
				log.Fatal("failed to retrieve impeached proposer from the given block header", "err", err, "num", numIter)
			}
		}

		// add the impeach status record
		err = ih.addHistory(addr, numIter, isImpeach)
		if err != nil {
			log.Fatal("failed to add impeach history to impeach history record", "err", err, "num", numIter)
		}
	}
}

// addHistory adds an impeach status record to a map, map[proposer]record
func (ih *impeachHistoryImpl) addHistory(addr common.Address, num uint64, isImpeach bool) error {
	ih.lock.Lock()
	defer ih.lock.Unlock()

	var (
		push  = false
		begin = outsetOf(num)
	)

	// if new history record comes, update it, else ignore.
	if num > ih.latest {
		ih.latest = num
		push = true
	}

	// if the outset updates, also update.
	if begin > ih.outset {
		ih.outset = begin
	}

	log.Debug("in add history", "begin", begin, "push", push, "addr", addr.Hex(), "num", num, "isImpeach", isImpeach)

	// if new and impeached record, push to record map
	if push && isImpeach {
		record, ok := ih.records[addr]
		if !ok {
			record = newRecord()
		}

		record.push(num)
		ih.records[addr] = record
	}
	return nil
}

// countHistory counts total impeach numbers of the given address after the outset.
func (ih *impeachHistoryImpl) countHistory(addr common.Address) int {
	ih.lock.RLock()
	defer ih.lock.RUnlock()

	record, ok := ih.records[addr]
	if !ok {
		return 0
	}

	outset := ih.outset
	return record.countAfter(outset)
}

// currentNumber returns latest recorded impeach status, (impeached or not)
func (ih *impeachHistoryImpl) currentNumber() uint64 {
	ih.lock.RLock()
	defer ih.lock.RUnlock()

	return ih.latest
}
