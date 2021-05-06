// Copyright 2018 The cphain authors
// This mode is designed for the mini env, you can use this mode to create a mini CPChain network.
// This network includes one validator and one proposal.

package configs

import (
	"math/big"
	"time"

	"github.com/ethereum/go-ethereum/common"
)

// mini configuration
var (
	// contract
	miniProxyContractRegister = common.HexToAddress("0xd4826927aa2dba7930117782ed183576ccebed93")
	MiniContractAddressMap    = map[string]common.Address{
		ContractRpt:       common.HexToAddress("0x275aC81051D8eE4738441Ee3Cb6F6fBfFf7830a2"),
		ContractRnode:     common.HexToAddress("0xE2A55B44997Df93e161d3fd2eE1118f1aaB8A263"),
		ContractAdmission: common.HexToAddress("0x33BbcA30eD34C87620C1F5A841a625DA37F480e8"),
		ContractCampaign:  common.HexToAddress("0x24E5D352A595dC92C4fFE428Dc29A0c0768b881D"),
		ContractNetwork:   common.HexToAddress("0xE7A90236868aF31eDa37595DEbc854ff1e0c2Bf6"),
	}

	// config
	miniDefaultCandidates = []common.Address{
		common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"), // #1
	}
	miniChainConfig = &ChainConfig{
		ChainID: big.NewInt(MiniChainId),
		Dpor: &DporConfig{
			Period:                MiniBlockPeriod,
			TermLen:               1,
			ViewLen:               3,
			FaultyNumber:          MiniFaultyValidatorsNumber,
			MaxInitBlockNumber:    MiniMaxInitBlockNumber,
			ProxyContractRegister: miniProxyContractRegister,
			Contracts:             MiniContractAddressMap,
			ImpeachTimeout:        time.Millisecond * MiniBlockPeriod,
		},
	}

	miniProposers = miniDefaultCandidates[0:1]

	miniValidators = []common.Address{
		common.HexToAddress("0x7b2f052a372951d02798853e39ee56c895109992"),
		common.HexToAddress("0x2f0176cc3a8617b6ddea6a501028fa4c6fc25ca1"),
		common.HexToAddress("0xe4d51117832e84f1d082e9fc12439b771a57e7b2"),
		common.HexToAddress("0x32bd7c33bb5060a85f361caf20c0bda9075c5d51"),
	}

	// CpchainBootnodes are the enode URLs of the P2P bootstrap nodes running on
	// the mini cpchain network.
	miniBootnodes = []string{
		"enode://5293dc8aaa5c2fcc7905c21391ce38f4f877722ff1918f4fa86379347ad8a244c2995631f89866693d05bf5c94493c247f02716f19a90689fa406189b03a5243@127.0.0.1:30381", // localhost
	}

	defaultMiniValidatorNodes = []string{
		"enode://9826a2f72c63eaca9b7f57b169473686f5a133dc24ffac858b4e5185a5eb60b144a414c35359585d9ea9d67f6fcca29578f9e002c89e94cc4bcc46a2b336c166@127.0.0.1:30317",
		"enode://7ce9c4fee12b12affbbe769a0faaa6e256bbae3374717fb94e1fb4be308fae3795c3abae023a587d8e14b35d278bd3d10916117bb8b3f5cfa4c951c5d56eeed7@127.0.0.1:30318",
		"enode://1db32421dc881357c282091960fdbd13f3635f8e3f87a953b6d9c429e53469727018bd0bb02da48acc4f1b4bec946b8f158705262b37163b4ab321a1c932d8f9@127.0.0.1:30319",
		"enode://fd0f365cec4e052040151f2a4a9ba23e8592acd3cacfdc4af2e8b6dbc6fb6b25ca088151889b19729d02c48e390de9682b316db2351636fdd1ee5ea1cd32bf46@127.0.0.1:30320",
	}
)
