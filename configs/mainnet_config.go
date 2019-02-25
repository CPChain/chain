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
	mainnetProxyContractRegister = common.HexToAddress("0xb3c12fe940589e349ea840f1d5a57741135bdba0")
	mainnetContractAddressMap    = map[string]common.Address{
		ContractCampaign:   common.HexToAddress("0x34eF33413C6578611CF39A9b8d59D5f1e724f240"),
		ContractProposer:   common.HexToAddress("0x7200badd33a52b3044232d8ca51b1e6f5a501a2e"),
		ContractRegister:   common.HexToAddress("0x2d2Fe846d6bCeB7B06a8bB8A847960AD518dA9c1"),
		ContractRpt:        common.HexToAddress("0x39514DFfb37d3BFB0223eab64A29c84f4944065B"),
		ContractPdash:      common.HexToAddress("0x7fdEFb08fA61bCE391B743eA44E5F73d6B301bAD"),
		ContractAdmission:  common.HexToAddress("0x3DCe838fded8631E1CcBC6373121d83e0a3C7dCD"),
		ContractPdashProxy: common.HexToAddress("0x2bF8186123489377E9e1E96cb0FFB9b66fB2317e"),
	}

	// config
	mainnetDefaultCandidates = []common.Address{
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
	mainnetChainConfig = &ChainConfig{
		ChainID: big.NewInt(MainnetChainId),
		Dpor: &DporConfig{
			Period:                MainnetBlockPeriod,
			TermLen:               4,
			ViewLen:               3,
			FaultyNumber:          MainnetFaultyValidatorsNumber,
			MaxInitBlockNumber:    DefaultMainnetMaxInitBlockNumber,
			ProxyContractRegister: mainnetProxyContractRegister,
			Contracts:             mainnetContractAddressMap,
			ImpeachTimeout:        time.Millisecond * DefaultBlockPeriod * 2,
		},
	}
	mainnetProposers = []common.Address{
		common.HexToAddress("0x9e61732d0b1c1674151a01ac0bba824c5b6258fb"),
		common.HexToAddress("0xaa6cf4f0338e04a40709dfa3c653efc6cd9e65c9"),
		common.HexToAddress("0x7170f578ca82897375f009ddea399df08f31bcff"),
		common.HexToAddress("0x4c61559aa727380e3fa516b6a7ae397b87ec2384"),
	}
	mainnetValidators = []common.Address{
		common.HexToAddress("0x0b2ee61452cc951565ed4b8eabff85c3f585c149"),
		common.HexToAddress("0x6a3678cac50b9266f82abe1a12bd26edc8e743a3"),
		common.HexToAddress("0xc6bfd405a99a39fa06f3cf0f568c3a2a40c29882"),
		common.HexToAddress("0xaee4ecd7edd59f5a2a0fe1fc786d217bea6ac3d9"),
		common.HexToAddress("0xd7be125f3c60105b44e3242f5c5509d6c993ebb8"), // #11
		common.HexToAddress("0x30a36525ca46504939e944e89422bdac745dd050"), // #12
		common.HexToAddress("0x8341844d109c938f70d1ff4e621bc8da097b8d83"), // #13
	}

	// coming soon ...
	mainnetBootnodes = []string{
		"enode://d9bd60488c269f1324ed7811341f4c81ce42ed0531852ea265148a6a7f4cb99d58c95a979de059c5052b1d38eb4462b775f8d8db40f92cf3828d884265176cde@127.0.0.1:30310", // localhost
	}

	//  coming soon ...
	defaultMainnetValidatorNodes = []string{
		"enode://2ddfb534019e6b446fb4465742f266d04fae661089e3dac6a4c841ad0fcf5569f8d049203079bb64e20d1a32fc84b584920839a2120cd5e8886744719452d936@127.0.0.1:30317",
		"enode://f2a460e5d5008d0ba8ec0744c90df9d1fc01553e00025af483995a15d89e773de18a37972c38bdcf47917fc820738455b85675bb51b026a75768c68d5540d053@127.0.0.1:30318",
		"enode://f3045792b9e9ad894cb36b488f1cf97065013cda9ef60f2b14840214683b3ef3dadf61450a9f677457c1a4b75a5b456947f48f3cb0019c7470cced9af1829993@127.0.0.1:30319",
		"enode://be14fce25a846bd5c91728fec7fb7071c98e2b9f8f4b710dbce79d8b6098592591ebeebfe6c59ee5bfd6f75387926f9342ae004d6ff8dcf97fc6d7e91e8f41be@127.0.0.1:30320",
		"enode://00e5229f3792264032a335759671996da3714f90f8d19defd0abce4e27515e7e644a76ae19b994f9b28b4d652826fa0766298b60db6df70aa2def7461c50d662@127.0.0.1:30321",
		"enode://369699f91013336e4ecf349aac4a4a6ee3957c7c7577996f9db821013e2e232ef8151e200cc2ab7ea9265121642b05b1cd21640d29e1e4bf8f6af737f353275c@127.0.0.1:30322",
		"enode://ee4c7418336745ed8a54da5fd8b151ade53b0b2a53b8e1d5eecfae483d15f5ff9e440155c47311dc826c44d44dce0080a6246204ed992f1e37d7094df4289169@127.0.0.1:30323",
	}

	mainnetDeposit = big.NewInt(50)
)
