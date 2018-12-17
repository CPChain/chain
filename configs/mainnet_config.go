// Copyright 2018 The cphain authors
// Copyright 2016 The go-ethereum Authors

package configs

import (
	"math/big"
	"time"
)

// Mainnet configuration
var (
	// contract
	mainnetProxyContractRegister = devProxyContractRegister
	mainnetContractAddressMap    = devContractAddressMap

	// config
	mainnetDefaultCandidates = devDefaultCandidates
	mainnetChainConfig       = &ChainConfig{
		ChainID: big.NewInt(MainnetChainId),
		Dpor: &DporConfig{
			Period:                DefaultBlockPeriod,
			TermLen:               4,
			ViewLen:               3,
			ValidatorsLen:         DefaultValidatorsLen,
			MaxInitBlockNumber:    72,
			ProxyContractRegister: mainnetProxyContractRegister,
			Contracts:             mainnetContractAddressMap,
			ImpeachTimeout:        time.Nanosecond * DefaultBlockPeriod * 2,
		},
	}
	mainnetProposers  = devProposers
	mainnetValidators = devValidators
)
