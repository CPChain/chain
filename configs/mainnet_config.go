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
		ContractRpt:       common.HexToAddress("0x16cb35DD47421895215b01a41a8e424E6eb39235"),
		ContractRnode:     common.HexToAddress("0x76130DA5aA1851313a7555D3735BED76029560DA"),
		ContractAdmission: common.HexToAddress("0xB3178aa5f6B5ABDc534e5bDEEc70B7e36BBDa4e2"),
		ContractCampaign:  common.HexToAddress("0x2A186bE66Dd20c1699Add34A49A3019a93a7Fcd0"),
		ContractNetwork:   common.HexToAddress("0xFE4e9816C4B05D0be4fe1fb951FfAB44e3309418"),
	}

	// config
	mainnetDefaultCandidates = []common.Address{
		common.HexToAddress("0x50f8c76f6d8442c54905c74245ae163132b9f4ae"), // #1
		common.HexToAddress("0x8ab63651e6ce7eed40af33276011a5e2e1a533a2"), // #2
		common.HexToAddress("0x501f6cf7b2437671d770998e3b785474878fef1d"), // #3
		common.HexToAddress("0x9508e430ce672750bcf6bef9c4c0adf303b28c5c"), // #4
		common.HexToAddress("0x049295e2e925cec28ddeeb63507e654b6d317423"), // #5
		common.HexToAddress("0x8c65cb8568c4945d4b419af9066874178f19ba43"), // #6
		common.HexToAddress("0x4d1f1d14f303b746121564e3295e2957e74ea5d2"), // #14
		common.HexToAddress("0x73ae2b32ef3fad80707d4da0f49c675d3efc727c"), // #15
		common.HexToAddress("0x5a55d5ef67c047b5d748724f7401781ed0af65ed"), // #16
		common.HexToAddress("0x1f077085dfdfa4a65f8870e50348f277d6fcd97c"), // #17
		common.HexToAddress("0xcb6fb6a201d6c126f80053fe17ca45188e24fe2f"), // #18
		common.HexToAddress("0xfaf2a2cdc4da310b52ad7d8d86e8c1bd5d4c0bd0"), // #19
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
	mainnetProposers = mainnetDefaultCandidates

	mainnetValidators = []common.Address{
		common.HexToAddress("0x2effd798690059ed313fa7d08483bcfa7ea637be"), //#7
		common.HexToAddress("0x1f12dc7132c31dd26dfac3754b3a7ea0da1ea352"), //#8
		common.HexToAddress("0xca9463aa4b1157681421c72e052d2cf8b6498a38"), //#9
		common.HexToAddress("0xd08975bb4c17c8139cf5107e1fd896d46b7a848a"), //#10
		common.HexToAddress("0xce5eb5797e457cfa99f0bf2c994c46614bfb4feb"), // #11
		common.HexToAddress("0x15b5a0709ae8cf751377bf9e26b8340c7bb9162b"), // #12
		common.HexToAddress("0x1e693ea09b1593bd3c795186806121f5b69371b6"), // #13
	}

	mainnetBootnodes = []string{
		"enode://fac8239134ee0ae6a1d9a0035fd83157011ac27e6ed0c8b00bdd422e7f400b8333660255aac4a21c54df9548fdbeaa81e6216338d41809a9268118dd62e08764@b01.mainnet.cpc-servers.com:30310",
		"enode://c009b708a91abc610204acf46cea61358ec2113a2cf9e62e93b18639a40763af9853238b3162c62d07aeea0d8d5c6d91b08b88747a0bf4f737bb9a1230b3564b@b02.mainnet.cpc-servers.com:30310",
		"enode://c9581e453fa0d4f75529824811b8db7e168683cda737f24b0c3f44ae1242d924cc600c1f78fc7d077c80e9a3f824a47f4fa221327e741aae3a505493e059@b03.mainnet.cpc-servers.com:30310",
	}

	defaultMainnetValidatorNodes = []string{
		"enode://503dd5cd4a532635f484c3ea9abb906a3a286cc79112f670595f021da9a5570f1e984e9d3e8374084d8b6d136798ba771a01a76f80a6acd67ff824864ba67e0a@v01.mainnet.cpc-servers.com:30310",
		"enode://f64d08fac6acd07be96df3bcfa3f73128a328a374ccdb1d88b565c43662ab7248ab85548f89b319b5b964491e3e6f677a468c03111398c653183c310c3c22de4@v02.mainnet.cpc-servers.com:30310",
		"enode://196f9d87497b3e5de234eb6b35cdbafbf9851b006bac1246eaf71868464306fdeb971b5a182185ece04e747cc3e219376c72eb8df30b5d74918f7a7705ff6aaf@v03.mainnet.cpc-servers.com:30310",
		"enode://9d570a1366a75b45597a48f0ea8e0c7d2a5519fd23106d53629d69156176a58dbdfca57bdfb4dd205f02aaf85b6f02bbb70699adff6d56849ce140ac694021bf@v04.mainnet.cpc-servers.com:30310",
		"enode://6bc0cadbf3f60876a9b7da3f6f5bad406d484fffc414f993a9dfa6535c19b457c30287cd7e4ac43980efafd52499ebac151752b2f889f18d3247086a32f7f678@v05.mainnet.cpc-servers.com:30310",
		"enode://80945a6705944de57515a83258b4dedf939cf42ed5cdc240081ea4587c2227841e20b4d078c5923e01c3d8cb746a2569e8ac25933ab9f4f54c6e2a17af338005@v06.mainnet.cpc-servers.com:30310",
		"enode://01e620180eb2c0fc3d15e0de246fd897781a72eeaf7431a05dc082b2a3f0488eb297ce8d59e4c30d362e02152d300bbc3f7cd42306e8c7deab62677be1debdd4@v07.mainnet.cpc-servers.com:30310",
	}
)
