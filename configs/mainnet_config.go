// Copyright 2018 The cphain authors
// Copyright 2016 The go-ethereum Authors

package configs

import (
	"math/big"
	"time"

	"github.com/ethereum/go-ethereum/common"
)

// mainnet configuration
var (
	mainnetDefaultCandidates  = devDefaultCandidates
	mainnetContractAddressMap = devContractAddressMap
	mainnetChainConfig        = &ChainConfig{
		ChainID: big.NewInt(MainnetChainId),
		Dpor: &DporConfig{
			Period:                DefaultBlockPeriod,
			TermLen:               4,
			ViewLen:               3,
			ValidatorsLen:         4,
			MaxInitBlockNumber:    72,
			ProxyContractRegister: common.HexToAddress("0x1a9fae75908752d0abf4dca45ebcac311c376290"),
			Contracts:             devContractAddressMap,
			ImpeachTimeout:        time.Second * DefaultBlockPeriod * 2,
		},
	}
	mainnetProposers  = devProposers
	mainnetValidators = devValidators
)
