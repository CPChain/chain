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
			MaxInitBlockNumber:    DefaultMainnetMaxInitBlockNumber,
			ProxyContractRegister: mainnetProxyContractRegister,
			Contracts:             mainnetContractAddressMap,
			ImpeachTimeout:        time.Millisecond * DefaultBlockPeriod * 2,
		},
	}
	mainnetProposers  = devProposers
	mainnetValidators = devValidators

	// coming soon ...
	mainnetBootnodes = []string{
		"enode://5293dc8aaa5c2fcc7905c21391ce38f4f877722ff1918f4fa86379347ad8a244c2995631f89866693d05bf5c94493c247f02716f19a90689fa406189b03a5243@127.0.0.1:30310", // localhost
	}

	//  coming soon ...
	defaultMainnetValidatorNodes = []string{
		"enode://9826a2f72c63eaca9b7f57b169473686f5a133dc24ffac858b4e5185a5eb60b144a414c35359585d9ea9d67f6fcca29578f9e002c89e94cc4bcc46a2b336c166@127.0.0.1:30317",
		"enode://7ce9c4fee12b12affbbe769a0faaa6e256bbae3374717fb94e1fb4be308fae3795c3abae023a587d8e14b35d278bd3d10916117bb8b3f5cfa4c951c5d56eeed7@127.0.0.1:30318",
		"enode://1db32421dc881357c282091960fdbd13f3635f8e3f87a953b6d9c429e53469727018bd0bb02da48acc4f1b4bec946b8f158705262b37163b4ab321a1c932d8f9@127.0.0.1:30319",
		"enode://fd0f365cec4e052040151f2a4a9ba23e8592acd3cacfdc4af2e8b6dbc6fb6b25ca088151889b19729d02c48e390de9682b316db2351636fdd1ee5ea1cd32bf46@127.0.0.1:30320",
	}

	mainnetDeposit = big.NewInt(50)
)
