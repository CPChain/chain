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

package admission

import (
	"math"
	"time"

	"bitbucket.org/cpchain/chain/admission/ethash"
)

type workStatus = uint32

const maxNonce = math.MaxUint64

const (
	// AcIdle status done.
	AcIdle workStatus = iota + 1
	// AcRunning status running.
	AcRunning
)

// Config admission control's configuration.
type Config struct {
	EthashConfig ethash.Config
	CPUConfig    CPUConfig
	// CampaignContractAddress public campaign's contract address.
	// common.HexToAddress("0x1a9fAE75908752d0ABf4DCa45ebcaC311C376290")
	CampaignContractAddress string
	// Deposit to mortgage
	Deposit int64
	// MinimumRpt minimum rpt
	MinimumRpt int64
	// NumberOfCampaign wants to campaign times
	NumberOfCampaignTimes int64
}

// CPUConfig cpu pow config
type CPUConfig struct {
	Difficulty int64
	LifeTime   time.Duration
}

// DefaultCampaignContractAddress default campaign contract address
var DefaultCampaignContractAddress = "0x1a9fAE75908752d0ABf4DCa45ebcaC311C376290"

// DefaultEthashConfig default ethash config
var DefaultEthashConfig = ethash.Config{
	Difficulty:     int64(55),
	LifeTime:       1 * 60 * time.Second,
	CacheDir:       "ethash",
	CachesInMem:    2,
	CachesOnDisk:   3,
	DatasetsInMem:  1,
	DatasetsOnDisk: 2,
}

// DefaultCPUConfig default cpu config
var DefaultCPUConfig = CPUConfig{
	Difficulty: int64(55),
	LifeTime:   1 * 60 * time.Second,
}

// DefaultConfig default admission config.
var DefaultConfig = Config{
	CPUConfig:               DefaultCPUConfig,
	EthashConfig:            DefaultEthashConfig,
	CampaignContractAddress: DefaultCampaignContractAddress,
	Deposit:                 int64(50),
	MinimumRpt:              int64(50),
	NumberOfCampaignTimes:   int64(1),
}

// ProofInfo is used to send to contract
type ProofInfo struct {
	BlockNumber uint64 `json:"block_number"`
	CPUNonce    uint64 `json:"cpu_nonce"`
	MemoryNonce uint64 `json:"memory_nonce"`
}
