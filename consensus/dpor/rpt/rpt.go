package rpt

// this package collects all reputation calculation related information,
// then calculates the reputations of candidates.

import (
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/hashicorp/golang-lru"
)

var (
	extraVanity = 32 // Fixed number of extra-data prefix bytes reserved for signer vanity
	extraSeal   = 65 // Fixed number of extra-data suffix bytes reserved for signer seal
)

const (
	Created = iota
	SellerConfirmed
	ProxyFetched
	ProxyDelivered
	BuyerConfirmed
	Finished
	SellerRated
	BuyerRated
	AllRated
	Disputed
	Withdrawn
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

// This is used for sorting.
func (a RptList) Len() int      { return len(a) }
func (a RptList) Swap(i, j int) { a[i], a[j] = a[j], a[i] }
func (a RptList) Less(i, j int) bool {
	return a[i].Rpt < a[j].Rpt && a[i].Address.Big().Cmp(a[j].Address.Big()) < 0
}

// RptService provides methods to obtain all rpt related information from block txs and contracts.
type RptService interface {
	CalcRptInfoList(addresses []common.Address, number uint64) RptList
	CalcRptInfo(address common.Address, number uint64) Rpt
}

// BasicCollector is the default rpt collector
type RptServiceImpl struct {
	rptContract common.Address
	client      bind.ContractBackend

	rptcache *lru.ARCCache
}

const cacheSize = 10

//NewRptService creates a concrete RPT service instance.
func NewRptService(backend bind.ContractBackend, rptContractAddr common.Address) (RptService, error) {
	cache, _ := lru.NewARC(cacheSize)
	bc := &RptServiceImpl{
		client:      backend,
		rptContract: rptContractAddr,
		rptcache:    cache,
	}
	return bc, nil
}

// CalcRptInfoList returns reputation of
// the given addresses.
func (rs *RptServiceImpl) CalcRptInfoList(addresses []common.Address, number uint64) RptList {
	rpts := RptList{}
	for _, address := range addresses {
		rpts = append(rpts, rs.CalcRptInfo(address, number))
	}
	return rpts
}

// calcRptInfo return the Rpt of the rnode address
func (rs *RptServiceImpl) CalcRptInfo(address common.Address, blockNum uint64) Rpt {
	instance, err := dpor.NewRpt(rs.rptContract, rs.client)
	if err != nil {
		log.Fatal("New primitivesContract error")
	}
	rpt := int64(0)
	windowSize, err := instance.Window(nil)
	if err != nil {
		log.Fatal("Get windowSize error")
	}
	for i := int64(blockNum); i >= 0 && i >= int64(blockNum)-windowSize.Int64(); i-- {
		hash := RptHash(RptItems{Nodeaddress: address, Key: uint64(i)})
		rc, exists := rs.rptcache.Get(hash)
		if !exists {
			rptInfo, err := instance.GetRpt(nil, address, new(big.Int).SetInt64(i))
			if err != nil {
				log.Fatal("GetRpt error", "error", err)
			}
			rs.rptcache.Add(hash, Rpt{Address: address, Rpt: rptInfo.Int64()})
			rpt += rptInfo.Int64()
		} else {
			if value, ok := rc.(Rpt); ok {
				rpt += value.Rpt
			}
		}
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
