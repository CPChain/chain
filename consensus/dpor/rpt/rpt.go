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
	"math/big"
	"strings"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/primitive_register"
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

const (
	cacheSize = 120
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

// NewRptService creates a concrete RPT service instance.
func NewRptService(backend bind.ContractBackend, rptContractAddr common.Address) (RptService, error) {
	log.Debug("rptContractAddr", "contractAddr", rptContractAddr.Hex())
	primitive_register.GetPrimitiveContractCheckerInstance().WaitInitCompleteUntilTimeout()

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
	instance, err := contracts.NewRpt(rs.rptContract, rs.client)
	log.Debug("calling to RPT contract", "contractAddr", rs.rptContract.Hex())
	if err != nil {
		log.Error("New primitivesContract error")
		return Rpt{Address: address, Rpt: minRptScore}
	}
	rpt := int64(0)
	windowSize, err := instance.Window(nil)
	if err != nil {
		log.Error("Get windowSize error", "error", err)
		return Rpt{Address: address, Rpt: minRptScore}
	}
	for i := int64(blockNum); i >= 0 && i >= int64(blockNum)-windowSize.Int64(); i-- {
		hash := RptHash(RptItems{Nodeaddress: address, Key: uint64(i)})
		rc, exists := rs.rptcache.Get(hash)
		if !exists {
			rptInfo, err := instance.GetRpt(nil, address, new(big.Int).SetInt64(i))
			if err != nil {
				log.Error("GetRpt error", "error", err, "address", address.Hex())
				return Rpt{Address: address, Rpt: minRptScore}
			}
			rs.rptcache.Add(hash, Rpt{Address: address, Rpt: rptInfo.Int64()})
			rpt += rptInfo.Int64()
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
