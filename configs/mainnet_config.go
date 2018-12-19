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
			MaxInitBlockNumber:    DefaultMaxInitBlockNumber,
			ProxyContractRegister: mainnetProxyContractRegister,
			Contracts:             mainnetContractAddressMap,
			ImpeachTimeout:        time.Nanosecond * DefaultBlockPeriod * 2,
		},
	}
	mainnetProposers  = devProposers
	mainnetValidators = devValidators

	// coming soon ...
	mainnetBootnodes = []string{
		"enode://5293dc8aaa5c2fcc7905c21391ce38f4f877722ff1918f4fa86379347ad8a244c2995631f89866693d05bf5c94493c247f02716f19a90689fa406189b03a5243@127.0.0.1:30310", // localhost
	}
)
