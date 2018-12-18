// Copyright 2018 The cphain authors
// Copyright 2016 The go-ethereum Authors

package configs

import (
	"math/big"
	"time"

	"github.com/ethereum/go-ethereum/common"
)

// Testnet configuration
var (
	// contract
	testnetProxyContractRegister = common.HexToAddress("0xa6a8ac0cad2150e076de638aa492042eeb823c6b")
	testnetContractAddressMap    = map[string]common.Address{
		ContractCampaign: common.HexToAddress("0x82102c2a09dee47d1ddcf298aef7877f99d787c4"),
		ContractProposer: common.HexToAddress("0x04686eb1c444e1a944b51f92aeb3efd918a350ca"),
		ContractRegister: common.HexToAddress("0x7a174062c5c8551649a86ae1b8a84282d901c2c3"),
		ContractRpt:      common.HexToAddress("0x2b11ca41a28571e22e242299dc308f08edd7f011"),
		ContractPdash:    common.HexToAddress("0x7be67ec2da5e15d394b19cab9497c307fc4fd424"),
	}

	// config
	testnetDefaultCandidates = []common.Address{
		common.HexToAddress("0x2a15146f434c0205cfae639de2ac4bb543539b24"), // #1
		common.HexToAddress("0xb436e2feffa76c30beb9d89e825281baa9956d4c"), // #2
		common.HexToAddress("0xf675b1e939892cad974a17da6bcd1cceae3b73dd"), // #3
		common.HexToAddress("0xe7a992e4187e95f28f8f69d44487fb16c465071c"), // #4
		common.HexToAddress("0x7326d5248928b87f63a80e424a1c6d39cb334624"), // #5
		common.HexToAddress("0x2661177788fe63888e93cf18b5e4e31306a01170"), // #6
	}
	testnetChainConfig = &ChainConfig{
		ChainID: big.NewInt(TestnetChainId),
		Dpor: &DporConfig{
			Period:                DefaultBlockPeriod,
			TermLen:               4,
			ViewLen:               3,
			ValidatorsLen:         DefaultValidatorsLen,
			MaxInitBlockNumber:    DefaultMaxInitBlockNumber,
			ProxyContractRegister: testnetProxyContractRegister,
			Contracts:             testnetContractAddressMap,
			ImpeachTimeout:        time.Nanosecond * DefaultBlockPeriod * 2,
		},
	}

	testnetProposers = testnetDefaultCandidates[0:4]

	testnetValidators = []common.Address{
		common.HexToAddress("0x177b2a835f27a8989dfca814b37d08c54e1de889"),
		common.HexToAddress("0x832062f84f982050c820b5ec986c1825d000ec8e"),
		common.HexToAddress("0x2da372d6026573aa5e1863ba3fa724a231c477d6"),
		common.HexToAddress("0x08e86c815665de506a210ff4b8e8572b8c201009"),
	}
)
