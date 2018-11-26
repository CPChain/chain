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
	"time"
)

type WorkStatus = uint32

const (
	CpuDifficulty     = 8
	MemoryDifficulty  = 8
	CpuWorkTimeout    = 10
	MemoryWorkTimeout = 10
)

const (
	Cpu    = "cpu"
	Memory = "memory"
)

// Config admission control's configuration.
type Config struct {
	CpuDifficulty     uint64
	CpuLifeTime       time.Duration
	MemoryDifficulty  uint64
	MemoryCpuLifeTime time.Duration
	// CampaignContractAddress public campaign's contract address.
	// common.HexToAddress("0x1a9fAE75908752d0ABf4DCa45ebcaC311C376290")
	CampaignContractAddress string
	// Deposit to mortgage
	Deposit int64
	// NumberOfCampaign wants to campaign times
	NumberOfCampaignTimes int64
}

// DefaultCampaignContractAddress default campaign contract address
// TODO @chengx delete it.  associate the address with the chain it's on, either mainnet or testnet
var DefaultCampaignContractAddress = "0x1a9fAE75908752d0ABf4DCa45ebcaC311C376290"

// DefaultConfig default admission config.
var DefaultConfig = Config{
	CpuDifficulty:           CpuDifficulty,
	CpuLifeTime:             time.Duration(CpuWorkTimeout * time.Second),
	MemoryDifficulty:        MemoryDifficulty,
	MemoryCpuLifeTime:       time.Duration(MemoryWorkTimeout * time.Second),
	CampaignContractAddress: DefaultCampaignContractAddress,
	// TODO @chengx no hardcoded numbers.
	Deposit:                 int64(50),
	NumberOfCampaignTimes:   int64(1),
}
