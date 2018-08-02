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

func (a RPTs) Len() int           { return len(a) }
func (a RPTs) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a RPTs) Less(i, j int) bool { return a[i].Rpt < a[j].Rpt }

// InfoCollector collects all rpt related information from block txs and contracts.
type InfoCollector interface {
	getRpt(address common.Address) RPT
	getRpts(addresses []common.Address) RPTs

	calcRptInfo(address common.Address) RPT
	getRptInfo(address common.Address) Info

	getChainRptInfo(address common.Address) ChainRptInfo
	getContractRptInfo(address common.Address) ContractRptInfo
}

// RPTer is the rpt collector
type RPTer struct {
}

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

func (r *RPTer) getRpt(address common.Address) RPT {
	return r.calcRptInfo(address)
}

func (r *RPTer) getRpts(addresses []common.Address) RPTs {
	rpts := RPTs{r.getRpt(addresses[0])}
	for i := 1; i < len(addresses); i++ {
		rpts = append(rpts, r.getRpt(addresses[i]))
	}
	return rpts
}

func (r *RPTer) calcRptInfo(address common.Address) RPT {
	alpha := 0.5
	beta := 0.5
	lambda := 0.5
	sigma := 0.5

	a := 0.5
	b := 0.5

	chainInfo := r.getChainRptInfo(address)
	contractInfo := r.getContractRptInfo(address)

	rpt := a*(alpha*chainInfo.CoinAge+beta*chainInfo.TxVolume) +
		b*(lambda*contractInfo.LeaderReward+sigma*contractInfo.UploadReward)
	return RPT{Address: address, Rpt: rpt}
}

func (r *RPTer) getChainRptInfo(address common.Address) ChainRptInfo {
	return ChainRptInfo{CoinAge: 50, TxVolume: 50}
}

func (r *RPTer) getContractRptInfo(address common.Address) ContractRptInfo {
	return ContractRptInfo{LeaderReward: 50.0, UploadReward: 50.0}
}

func (r *RPTer) getRptInfo(address common.Address) Info {
	return Info{
		ChainInfo:    r.getChainRptInfo(address),
		ContractInfo: r.getContractRptInfo(address),
	}
}
