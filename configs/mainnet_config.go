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
		ContractRpt:       common.HexToAddress("0x3fea6e441d9dbafb80f20333bd16d00e49179b33"),
		ContractRnode:     common.HexToAddress("0x76dbca2ced6d81e2f26a6657b436d340bb924874"),
		ContractAdmission: common.HexToAddress("0x45621603c070b051c0fc337294caa7b4a21a8b79"),
		ContractCampaign:  common.HexToAddress("0x4e0ab103714c14d2e3b3a4d9d7355f6a01534242"),
		ContractNetwork:   common.HexToAddress("0x951c57619ad1f7dcf2eb5f7078ee7264c9cf8ef8"),
	}

	// config
	mainnetDefaultCandidates = []common.Address{
		common.HexToAddress("0x27c3500c8a493a152f1dfdec162c422b3678b03e"), // #1
		common.HexToAddress("0xf285996f36aa76adf637c60f2005da637efd71aa"), // #2
		common.HexToAddress("0x50bf9d407d8e30b8124f3711df97611d76d45699"), // #3
		common.HexToAddress("0x99fc3138ff48a4fae3a0e65c6f83266a5284a683"), // #5
		common.HexToAddress("0xf6f59e901b3cd551f1753dfe80ab806bb0046b30"), // #4
		common.HexToAddress("0xa3a0fe044eb8ce1731ed99ca0901a795abf58da8"), // #6
		common.HexToAddress("0x45f40e0c7135d86d92a88443a160045a2897436e"), // #14
		common.HexToAddress("0x0005efc08c5ff71c3538ebc85b1bb93c377cef14"), // #15
		common.HexToAddress("0x46ac4607b5334b5dc7cd671b0c11c5ffa81324f6"), // #16
		common.HexToAddress("0x1573ce2ab9a0113d25ce5e7a74b564a02f9058ad"), // #17
		common.HexToAddress("0x01cf3229840fc212d54df720cdae3e6d04320a9c"), // #18
		common.HexToAddress("0xaa8ad61eb978bbde0b6f69d2cd3033755d8f9d04"), // #19
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
		common.HexToAddress("0xbb0100151e0e6fde0a79f83f20b979f6453082b0"), //#7
		common.HexToAddress("0x890f2f614f4ba5bcc1d8310aeb0e4e2891b49456"), //#8
		common.HexToAddress("0x888ff37e1f16fdafae305db34a2b82b72efd4b13"), //#9
		common.HexToAddress("0xbb8be04ca968670f9f690e98cc5d668c3631e42e"), //#10
		common.HexToAddress("0x3e9612220d39026f5200ff28753f43dd967f09fd"), // #11
		common.HexToAddress("0x1975ec9cd13de83530b29f2917c7f5c0c04f995c"), // #12
		common.HexToAddress("0xa9c2f9e7ea9570046b0bccb3b6438b0153b79f16"), // #13
	}

	mainnetBootnodes = []string{
		"enode://249896cf064519e0eaa54f47a5dd5bcb5d24961b03d5a2ad170675b52f43c65ea9de9edaca1a2dcd2422145c0d2f29d0bcb96a7e9bc54469fabdc09d9f3745f6@b01.mainnet.cpc-servers.com:30310",
		"enode://7ca533ed0bd212a92798c0a3eae59696bd7c20e62f4c44296b2ff7e19d93db6348519516955d562f94ca644b6b8f230e69a387163564845ad29301eca5e712a2@b02.mainnet.cpc-servers.com:30310",
		"enode://95e9f0dca6694fd994865faa71444b7880b574f20fcd10373a2c710e4de747c622a826cffab7b7505e0f6501a0884e67bdc3282ec0f8b73ee07ae7281d05a041@b03.mainnet.cpc-servers.com:30310",
	}

	defaultMainnetValidatorNodes = []string{
		"enode://ff705283b1fce33b378ec074971b50225eb59e98e3baa86f2c6f8cf45e0c634b63cd374a35b0ea9d32de99270c22852e94216b759d90e3c5f41dff9e38312a35@v01.mainnet.cpc-servers.com:30310",
		"enode://687cad5b3374eb0eefc7c77b1997a553344c5b5c4d63bd7a73eb17fb0ef4de800f47dd2a75583b004ee7afbabad3b77795f866529a751cac8f34bde1536bdfcc@v02.mainnet.cpc-servers.com:30310",
		"enode://de6402c71633fb740adc3caa792d2870bea35c888fec00038a8be8558dae2f999dc8451d6b92773dd1c967e9a34374f782eaa042e6ce2989d00082ed492fc4c4@v03.mainnet.cpc-servers.com:30310",
		"enode://078cbb93e251732112fbbfa6059bb50f77dd20dbf3156ebfe66bc8f6fd70cab3aed2c94557079aa5f6ed40ab4fbd8585be5a7db49709c88aeb7e92697be788df@v04.mainnet.cpc-servers.com:30310",
		"enode://3d46dff54508bb08e2e5a9856605ad7bc15b1646eeeba30a882c9352a1ea7cdfbea97993c7b984897856fda9ef154b276a8ed73fbac537fba00b2fe9f670096e@v05.mainnet.cpc-servers.com:30310",
		"enode://33e4739bb516a475ea8c823d305c033c7f3e2fe18883ce5d50e4f1f7c5113bc9c97a38d2f6e95db6bd951cb568fdd42075df341d0da325de43496114110c953a@v06.mainnet.cpc-servers.com:30310",
		"enode://1e19d838d202b08fba42a7f329a2b7c79bbd5442895858ea7e494ebfa452e1fad1e39abb70ab541560265692a3fb6a355bfbcbfadb08beea242aee9568bf5707@v07.mainnet.cpc-servers.com:30310",
	}
)
