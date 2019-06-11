// Copyright 2018 The cphain authors
// Copyright 2016 The go-ethereum Authors

package configs

import (
	"math/big"
	"time"

	"github.com/ethereum/go-ethereum/common"
)

// testMainnet configuration
var (
	// contract
	testMainnetProxyContractRegister = common.HexToAddress("0xd4826927aa2dba7930117782ed183576ccebed93")

	TestMainnetContractAddressMap = map[string]common.Address{
		ContractRpt:       common.HexToAddress("0x7e9925bea4af2ebea96dd8ba9894d4503e6c0278"),
		ContractRnode:     common.HexToAddress("0xd4826927aa2dba7930117782ed183576ccebed93"),
		ContractAdmission: common.HexToAddress("0xa5e0ea2a14d91031986c2f25f6e724beeeb66781"),
		ContractCampaign:  common.HexToAddress("0xf26b6864749cde85a29afea57ffeae115b24b505"),
		ContractNetwork:   common.HexToAddress("0xe30363ffce7f560cb69b7d9254daeb35de8c0f84"),
	}

	// config
	testMainnetDefaultCandidates = []common.Address{
		common.HexToAddress("0x9e61732d0b1c1674151a01ac0bba824c5b6258fb"), // #1
		common.HexToAddress("0xaa6cf4f0338e04a40709dfa3c653efc6cd9e65c9"), // #2
		common.HexToAddress("0x7170f578ca82897375f009ddea399df08f31bcff"), // #3
		common.HexToAddress("0x4c61559aa727380e3fa516b6a7ae397b87ec2384"), // #5
		common.HexToAddress("0xc5b481361bbcabb96ed0c835cee69b471449f49c"), // #4
		common.HexToAddress("0x6e7fdba0fe5067a25a3cf1df90429e3c949411e3"), // #6

		common.HexToAddress("0x27e81a296f5b80d319d2f3008f2d5998530e79e4"), // #14
		common.HexToAddress("0x52e584b4fba8688eb7edcabb18e65661a99acc67"), // #15
		common.HexToAddress("0x030352bba36c0c7cec8669f64a26d96d5d679bdb"), // #16
		common.HexToAddress("0xf561ebb8a40814c1cf3cc0a628df5a1bd7663b26"), // #17
		common.HexToAddress("0xca8e011de0edea4929328bb86e35daa686c47ed0"), // #18
		common.HexToAddress("0xcc9cd266776b331fd424ea14dc30fc8561bec628"), // #19
	}
	testMainnetChainConfig = &ChainConfig{
		ChainID: big.NewInt(TestMainnetChainId),
		Dpor: &DporConfig{
			Period:                TestMainnetBlockPeriod,
			TermLen:               12,
			ViewLen:               3,
			FaultyNumber:          TestMainnetFaultyValidatorsNumber,
			MaxInitBlockNumber:    DefaultTestMainnetMaxInitBlockNumber,
			ProxyContractRegister: testMainnetProxyContractRegister,
			Contracts:             TestMainnetContractAddressMap,
			ImpeachTimeout:        time.Millisecond * TestMainnetBlockPeriod,
		},
	}
	testMainnetProposers = []common.Address{
		common.HexToAddress("0x9e61732d0b1c1674151a01ac0bba824c5b6258fb"), // #1
		common.HexToAddress("0xaa6cf4f0338e04a40709dfa3c653efc6cd9e65c9"), // #2
		common.HexToAddress("0x7170f578ca82897375f009ddea399df08f31bcff"), // #3
		common.HexToAddress("0x4c61559aa727380e3fa516b6a7ae397b87ec2384"), // #5
		common.HexToAddress("0xc5b481361bbcabb96ed0c835cee69b471449f49c"), // #4
		common.HexToAddress("0x6e7fdba0fe5067a25a3cf1df90429e3c949411e3"), // #6

		common.HexToAddress("0x27e81a296f5b80d319d2f3008f2d5998530e79e4"), // #14
		common.HexToAddress("0x52e584b4fba8688eb7edcabb18e65661a99acc67"), // #15
		common.HexToAddress("0x030352bba36c0c7cec8669f64a26d96d5d679bdb"), // #16
		common.HexToAddress("0xf561ebb8a40814c1cf3cc0a628df5a1bd7663b26"), // #17
		common.HexToAddress("0xca8e011de0edea4929328bb86e35daa686c47ed0"), // #18
		common.HexToAddress("0xcc9cd266776b331fd424ea14dc30fc8561bec628"), // #19
	}
	testMainnetValidators = []common.Address{
		common.HexToAddress("0x0b2ee61452cc951565ed4b8eabff85c3f585c149"),
		common.HexToAddress("0x6a3678cac50b9266f82abe1a12bd26edc8e743a3"),
		common.HexToAddress("0xc6bfd405a99a39fa06f3cf0f568c3a2a40c29882"),
		common.HexToAddress("0xaee4ecd7edd59f5a2a0fe1fc786d217bea6ac3d9"),
		common.HexToAddress("0xd7be125f3c60105b44e3242f5c5509d6c993ebb8"), // #11
		common.HexToAddress("0x30a36525ca46504939e944e89422bdac745dd050"), // #12
		common.HexToAddress("0x8341844d109c938f70d1ff4e621bc8da097b8d83"), // #13
	}

	testMainnetBootnodes = []string{
		"enode://d9bd60488c269f1324ed7811341f4c81ce42ed0531852ea265148a6a7f4cb99d58c95a979de059c5052b1d38eb4462b775f8d8db40f92cf3828d884265176cde@b01.mainnet.cpc-servers.com:30381",
		"enode://775cedbf2026c065b67fc80a38995c2999d5b3c1f3a80695115b2606ad4025dacae6947034c89032453c0a71d8b49465f167e9c3b0e85a8cf9b4281e1cc198e4@b02.mainnet.cpc-servers.com:30382",
		"enode://b21a1567059168e3cecc7d5c60217cd73dc5b299c3865f2f9eea621a93e7e8bb266f7ade0b1db28160686c740be6de4c1000ef449d7cd8c97388eca1790bc61a@b03.mainnet.cpc-servers.com:30383",
		"enode://fb56640fb3b8dec3473ea3906ef59b97c4f7956d86be27ed65908fa706d2fbe91800b7a221ba45127cbe4b5eb26291f7fbd3984cdeab587d6fb53535ce4e0069@b04.mainnet.cpc-servers.com:30384",
	}

	defaultTestMainnetValidatorNodes = []string{
		"enode://2ddfb534019e6b446fb4465742f266d04fae661089e3dac6a4c841ad0fcf5569f8d049203079bb64e20d1a32fc84b584920839a2120cd5e8886744719452d936@v01.mainnet.cpc-servers.com:30317",
		"enode://f2a460e5d5008d0ba8ec0744c90df9d1fc01553e00025af483995a15d89e773de18a37972c38bdcf47917fc820738455b85675bb51b026a75768c68d5540d053@v02.mainnet.cpc-servers.com:30318",
		"enode://f3045792b9e9ad894cb36b488f1cf97065013cda9ef60f2b14840214683b3ef3dadf61450a9f677457c1a4b75a5b456947f48f3cb0019c7470cced9af1829993@v03.mainnet.cpc-servers.com:30319",
		"enode://be14fce25a846bd5c91728fec7fb7071c98e2b9f8f4b710dbce79d8b6098592591ebeebfe6c59ee5bfd6f75387926f9342ae004d6ff8dcf97fc6d7e91e8f41be@v04.mainnet.cpc-servers.com:30320",
		"enode://00e5229f3792264032a335759671996da3714f90f8d19defd0abce4e27515e7e644a76ae19b994f9b28b4d652826fa0766298b60db6df70aa2def7461c50d662@v05.mainnet.cpc-servers.com:30321",
		"enode://369699f91013336e4ecf349aac4a4a6ee3957c7c7577996f9db821013e2e232ef8151e200cc2ab7ea9265121642b05b1cd21640d29e1e4bf8f6af737f353275c@v06.mainnet.cpc-servers.com:30322",
		"enode://ee4c7418336745ed8a54da5fd8b151ade53b0b2a53b8e1d5eecfae483d15f5ff9e440155c47311dc826c44d44dce0080a6246204ed992f1e37d7094df4289169@v07.mainnet.cpc-servers.com:30323",
	}

	testMainnetDeposit = big.NewInt(50)
)
