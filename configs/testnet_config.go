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

	testnetContractAddressMap = map[string]common.Address{
		ContractAdmission: common.HexToAddress("0x82102c2A09DEe47D1DDcf298AeF7877F99d787c4"),
		ContractCampaign:  common.HexToAddress("0x2B11cA41A28571e22e242299dC308f08EDD7F011"),
		ContractRpt:       common.HexToAddress("0x7a174062c5C8551649A86AE1b8a84282D901C2C3"),
		ContractRnode:     common.HexToAddress("0xF0f87e064C76674fE7c4dDceE3603AFC67998658"),
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
			Period:                TestnetBlockPeriod,
			TermLen:               4,
			ViewLen:               3,
			FaultyNumber:          TestnetFaultyValidatorsNumber,
			MaxInitBlockNumber:    DefaultTestnetMaxInitBlockNumber,
			ProxyContractRegister: testnetProxyContractRegister,
			Contracts:             testnetContractAddressMap,
			ImpeachTimeout:        time.Millisecond * TestnetBlockPeriod * 2,
		},
	}

	testnetProposers = testnetDefaultCandidates[0:4]

	testnetValidators = []common.Address{
		common.HexToAddress("0x177b2a835f27a8989dfca814b37d08c54e1de889"),
		common.HexToAddress("0x832062f84f982050c820b5ec986c1825d000ec8e"),
		common.HexToAddress("0x2da372d6026573aa5e1863ba3fa724a231c477d6"),
		common.HexToAddress("0x08e86c815665de506a210ff4b8e8572b8c201009"),
	}

	testnetBootnodes = []string{
		"enode://18c444f813e3fbef9848748306a4a4b2fa2d90090a21e59c1dcdfa55a7435a18abaabffcd205fa976a2f4f9b1822ffd361b1e53bcef6b052823dd442b1722bf8@13.250.251.238:32000",
		"enode://9eedb4aa96949a2db1307a5860e604f5149a2933b82f70c7ac3080362db170a17513de101e39d36634994a22003c1f77980699d72636d9f747ece888e0c98895@52.74.85.139:32000",
	}

	// fixed ip
	defaultTestnetValidatorNodes = []string{
		// 7-"0x177b2a835f27a8989dfca814b37d08c54e1de889"
		"enode://5f11492af45df3c06fbdc435e4a66615baa58dc58a4918a3b693bf67c5baad4098ea5e0ca63a26ed55890865b8aa30550727ebff32b6826b72ad5c9dd28b4313@13.228.120.167:30317",
		// 8-"0x832062f84f982050c820b5ec986c1825d000ec8e"
		"enode://f22094e4153d73d304d0e362704ecfec5fa928e56b62703b599a66e445c7bfa5b7a525118dc7e41fdf98267e428bda4d98cb3405f50ae509add6fc5aa87c98b9@54.254.165.164:30318",
		// 9-"0x2da372d6026573aa5e1863ba3fa724a231c477d6"
		"enode://13925c2c99a2bc8ebb05d0946ee673d18fb1e2905b3e1e7ea4c840dd6cac5fc769ac54d1c791b158dbba3734494422fb0110aac4384f932d214aba69e0b49518@52.77.100.6:30319",
		// 10-"0x08e86c815665de506a210ff4b8e8572b8c201009"
		"enode://d4175e2c796a6591e52e788483261bb54cfc337e0ba881f033cafd12a3ea94d22f3c84fa8652a343b2cb155b6443d3494a9010a1b993e63841374e9311382513@3.0.229.150:30320",
	}

	testnetDeposit = big.NewInt(50)
)
