package rpt

import (
	"fmt"
	"math"
	"sort"
	"strings"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
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
