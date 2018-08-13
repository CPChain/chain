package rpt

// this package collects all reputation calculation related information,
// then calculates the reputations of candidates.

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

// Collector collects all rpt related information from block txs and contracts.
type Collector interface {
	GetRpt(address common.Address) RPT
	GetRpts(addresses []common.Address) RPTs

	GetRptInfo(address common.Address) Info
	GetRptInfos(addresses common.Address) map[common.Address]Info

	calcRptInfo(address common.Address) RPT

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

// GetRpt returns reputation of the given address.
func (bc *BasicCollector) GetRpt(address common.Address) RPT {
	return bc.calcRptInfo(address)
}

// GetRpts returns reputation list of given addresses.
func (bc *BasicCollector) GetRpts(addresses *[]common.Address) RPTs {
	rpts := RPTs{}
	for i := 0; i < len(*addresses); i++ {
		rpts = append(rpts, bc.GetRpt((*addresses)[i]))
	}
	return rpts
}

// GetRptInfo returns reputation info of given address.
func (bc *BasicCollector) GetRptInfo(address common.Address) Info {
	return Info{
		ChainInfo:    bc.getChainRptInfo(address),
		ContractInfo: bc.getContractRptInfo(address),
	}
}

// GetRptInfos returns reputation info of given address.
func (bc *BasicCollector) GetRptInfos(addresses *[]common.Address) map[common.Address]Info {
	infos := make(map[common.Address]Info)
	for _, address := range *addresses {
		infos[address] = bc.GetRptInfo(address)
	}
	return infos
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
