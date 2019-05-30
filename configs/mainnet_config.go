// Copyright 2018 The cphain authors
// Copyright 2016 The go-ethereum Authors

package configs

import (
	"math/big"
	"time"

	"github.com/ethereum/go-ethereum/common"
)

// Mainnet configuration
var (
	// contract
	mainnetProxyContractRegister = common.HexToAddress("0xd4826927aa2dba7930117782ed183576ccebed93")

	MainnetContractAddressMap = map[string]common.Address{
		ContractRpt:       common.HexToAddress("0x5ae4bddaf1d12baea98ebdf158c5ce3c53d21957"),
		ContractRnode:     common.HexToAddress("0xab11ddf548e4ec7e1ed0a375a9eb34445cdee856"),
		ContractAdmission: common.HexToAddress("0xd8cf29d5d77ce4a7bbf99ca8c665e39760c9dbe3"),
		ContractCampaign:  common.HexToAddress("0xb9a0ca9f8f1c55124157419c956d2ac6b6a94672"),
	}

	// config
	mainnetDefaultCandidates = []common.Address{
		common.HexToAddress("0x5f1fa0804bf76f71d5cfb621fac1f6fe27c8e80e"), // #1
		common.HexToAddress("0xb5edbc5a1e680e660dc78659613df7704bc198d2"), // #2
		common.HexToAddress("0x3868a7b3c55ac0d4f85fc869a2a444ae0f39a1e7"), // #3
		common.HexToAddress("0xf7b77be329185194520fc4447ea527217eae3974"), // #5
		common.HexToAddress("0x9ffa9e60feaab7acdb460c4b938d5d57b19b2e10"), // #4
		common.HexToAddress("0x352201b0e6b19b6c7e0fda80c0c3d462bcc0b81f"), // #6

		common.HexToAddress("0xd5a344b55a85b02c285fa4340dff4f54af0cb71f"), // #14
		common.HexToAddress("0x809471f4794c633dd6c9d4b02c6c2c3fb7bdf01f"), // #15
		common.HexToAddress("0xd0d39b67cad41642920fa0db66232709a8ce12c7"), // #16
		common.HexToAddress("0x15676f1f87d0c64cac3892afc4268490b4bd3243"), // #17
		common.HexToAddress("0x9e59ef188eb3e40e0540b713310fe4de70252ded"), // #18
		common.HexToAddress("0x360db7f7b3d6db2a9c97738075dca2c4f668382a"), // #19
	}
	mainnetChainConfig = &ChainConfig{
		ChainID: big.NewInt(MainnetChainId),
		Dpor: &DporConfig{
			Period:                MainnetBlockPeriod,
			TermLen:               12,
			ViewLen:               3,
			FaultyNumber:          MainnetFaultyValidatorsNumber,
			MaxInitBlockNumber:    DefaultMainnetMaxInitBlockNumber,
			ProxyContractRegister: mainnetProxyContractRegister,
			Contracts:             MainnetContractAddressMap,
			ImpeachTimeout:        time.Millisecond * MainnetBlockPeriod,
		},
	}
	mainnetProposers = []common.Address{
		common.HexToAddress("0x5f1fa0804bf76f71d5cfb621fac1f6fe27c8e80e"), // #1
		common.HexToAddress("0xb5edbc5a1e680e660dc78659613df7704bc198d2"), // #2
		common.HexToAddress("0x3868a7b3c55ac0d4f85fc869a2a444ae0f39a1e7"), // #3
		common.HexToAddress("0xf7b77be329185194520fc4447ea527217eae3974"), // #5
		common.HexToAddress("0x9ffa9e60feaab7acdb460c4b938d5d57b19b2e10"), // #4
		common.HexToAddress("0x352201b0e6b19b6c7e0fda80c0c3d462bcc0b81f"), // #6

		common.HexToAddress("0xd5a344b55a85b02c285fa4340dff4f54af0cb71f"), // #14
		common.HexToAddress("0x809471f4794c633dd6c9d4b02c6c2c3fb7bdf01f"), // #15
		common.HexToAddress("0xd0d39b67cad41642920fa0db66232709a8ce12c7"), // #16
		common.HexToAddress("0x15676f1f87d0c64cac3892afc4268490b4bd3243"), // #17
		common.HexToAddress("0x9e59ef188eb3e40e0540b713310fe4de70252ded"), // #18
		common.HexToAddress("0x360db7f7b3d6db2a9c97738075dca2c4f668382a"), // #19
	}
	mainnetValidators = []common.Address{
		common.HexToAddress("0x422dd016ccad93deb8ffe07416827371c37cbfe6"), //#7
		common.HexToAddress("0x3119d0a401ba28eb5b8269b03cdf73e1ff8942eb"), //#8
		common.HexToAddress("0x7ef70538c237e571ef35cdc600d2d01cdac3af27"), //#9
		common.HexToAddress("0x9d6ceb3827e6a276ce655bda7281ccff97364d44"), //#10
		common.HexToAddress("0x274ce385b87681e44c716001017e3e58c4b6864a"), // #11
		common.HexToAddress("0xfe1fedc1205a4484d4981b690ab8b7fdabd57890"), // #12
		common.HexToAddress("0x37163cba895198757c222f1e836d92cc1b39480f"), // #13
	}

	mainnetBootnodes = []string{
		"enode://d9bd60488c269f1324ed7811341f4c81ce42ed0531852ea265148a6a7f4cb99d58c95a979de059c5052b1d38eb4462b775f8d8db40f92cf3828d884265176cde@b01.mainnet.cpc-servers.com:30381",
		"enode://775cedbf2026c065b67fc80a38995c2999d5b3c1f3a80695115b2606ad4025dacae6947034c89032453c0a71d8b49465f167e9c3b0e85a8cf9b4281e1cc198e4@b02.mainnet.cpc-servers.com:30382",
		"enode://b21a1567059168e3cecc7d5c60217cd73dc5b299c3865f2f9eea621a93e7e8bb266f7ade0b1db28160686c740be6de4c1000ef449d7cd8c97388eca1790bc61a@b03.mainnet.cpc-servers.com:30383",
		"enode://fb56640fb3b8dec3473ea3906ef59b97c4f7956d86be27ed65908fa706d2fbe91800b7a221ba45127cbe4b5eb26291f7fbd3984cdeab587d6fb53535ce4e0069@b04.mainnet.cpc-servers.com:30384",
	}

	defaultMainnetValidatorNodes = []string{
		"enode://2ddfb534019e6b446fb4465742f266d04fae661089e3dac6a4c841ad0fcf5569f8d049203079bb64e20d1a32fc84b584920839a2120cd5e8886744719452d936@v01.mainnet.cpc-servers.com:30317",
		"enode://f2a460e5d5008d0ba8ec0744c90df9d1fc01553e00025af483995a15d89e773de18a37972c38bdcf47917fc820738455b85675bb51b026a75768c68d5540d053@v02.mainnet.cpc-servers.com:30318",
		"enode://f3045792b9e9ad894cb36b488f1cf97065013cda9ef60f2b14840214683b3ef3dadf61450a9f677457c1a4b75a5b456947f48f3cb0019c7470cced9af1829993@v03.mainnet.cpc-servers.com:30319",
		"enode://be14fce25a846bd5c91728fec7fb7071c98e2b9f8f4b710dbce79d8b6098592591ebeebfe6c59ee5bfd6f75387926f9342ae004d6ff8dcf97fc6d7e91e8f41be@v04.mainnet.cpc-servers.com:30320",
		"enode://00e5229f3792264032a335759671996da3714f90f8d19defd0abce4e27515e7e644a76ae19b994f9b28b4d652826fa0766298b60db6df70aa2def7461c50d662@v05.mainnet.cpc-servers.com:30321",
		"enode://369699f91013336e4ecf349aac4a4a6ee3957c7c7577996f9db821013e2e232ef8151e200cc2ab7ea9265121642b05b1cd21640d29e1e4bf8f6af737f353275c@v06.mainnet.cpc-servers.com:30322",
		"enode://ee4c7418336745ed8a54da5fd8b151ade53b0b2a53b8e1d5eecfae483d15f5ff9e440155c47311dc826c44d44dce0080a6246204ed992f1e37d7094df4289169@v07.mainnet.cpc-servers.com:30323",
	}

	mainnetDeposit = big.NewInt(50)
)
