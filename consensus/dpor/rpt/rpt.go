// this package collects all reputation calculation related information,
// then calculates the reputations of candidates.
package rpt

import (
	"github.com/ethereum/go-ethereum/common"
)

// RPT defines the name and reputation pair.
type RPT struct {
	Address common.Address
	Rpt     float64
}

// RPTs is an array of RPT.
type RPTs []RPT

// This is used for sorting.
func (a RPTs) Len() int           { return len(a) }
func (a RPTs) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a RPTs) Less(i, j int) bool { return a[i].Rpt < a[j].Rpt }

// InfoCollector collects all rpt related information from block txs and contracts.
type Collector interface {
	getRpt(address common.Address) RPT
	getRpts(addresses []common.Address) RPTs

	calcRptInfo(address common.Address) RPT
	getRptInfo(address common.Address) Info

	getChainRptInfo(address common.Address) ChainRptInfo
	getContractRptInfo(address common.Address) ContractRptInfo
}

// BasicCollector is the default rpt collector
type BasicCollector struct{}

// ChainRptInfo is the rpt info from chain.
type ChainRptInfo struct {
	CoinAge  float64
	TxVolume float64
}

// ContractRptInfo is the rpt info from contracts.
type ContractRptInfo struct {
	LeaderReward float64
	// proxyReward  float64
	UploadReward float64
}

// Info is the whole rpt info.
type Info struct {
	ChainInfo    ChainRptInfo
	ContractInfo ContractRptInfo
}

func (bc *BasicCollector) getRpt(address common.Address) RPT {
	return bc.calcRptInfo(address)
}

func (bc *BasicCollector) getRpts(addresses []common.Address) RPTs {
	rpts := RPTs{bc.getRpt(addresses[0])}
	for i := 1; i < len(addresses); i++ {
		rpts = append(rpts, bc.getRpt(addresses[i]))
	}
	return rpts
}

func (bc *BasicCollector) calcRptInfo(address common.Address) RPT {
	alpha := 0.5
	beta := 0.5
	lambda := 0.5
	sigma := 0.5

	a := 0.5
	b := 0.5

	chainInfo := bc.getChainRptInfo(address)
	contractInfo := bc.getContractRptInfo(address)

	rpt := a*(alpha*chainInfo.CoinAge+beta*chainInfo.TxVolume) +
		b*(lambda*contractInfo.LeaderReward+sigma*contractInfo.UploadReward)
	return RPT{Address: address, Rpt: rpt}
}

func (bc *BasicCollector) getChainRptInfo(address common.Address) ChainRptInfo {
	return ChainRptInfo{CoinAge: 50, TxVolume: 50}
}

func (bc *BasicCollector) getContractRptInfo(address common.Address) ContractRptInfo {
	return ContractRptInfo{LeaderReward: 50.0, UploadReward: 50.0}
}

func (bc *BasicCollector) getRptInfo(address common.Address) Info {
	return Info{
		ChainInfo:    bc.getChainRptInfo(address),
		ContractInfo: bc.getContractRptInfo(address),
	}
}
