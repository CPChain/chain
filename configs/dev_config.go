// Copyright 2018 The cphain authors
// Copyright 2016 The go-ethereum Authors

package configs

import (
	"math/big"
	"time"

	"github.com/ethereum/go-ethereum/common"
)

// dev configuration
var (
	// contract
	devProxyContractRegister = common.HexToAddress("0x1a9fae75908752d0abf4dca45ebcac311c376290")
	devContractAddressMap    = map[string]common.Address{
		ContractCampaign: common.HexToAddress("0x0ddf4057eedfb80d58029be49bab09bbc45bc500"),
		ContractProposer: common.HexToAddress("0x310236762f36bf0f69f792bd9fb08b5c679aa3f1"),
		ContractRegister: common.HexToAddress("0x019cc04ff9d88529b9e58ff26bfc53bce060e915"),
		ContractRpt:      common.HexToAddress("0x82104907aa699b2982fc46f38fd8c915d03cdb8d"),
		ContractPdash:    common.HexToAddress("0xaaae743244a7a5116470df8bd398e7d562ae8881"),
	}

	// config
	devDefaultCandidates = []common.Address{
		common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092"), // #2
		common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"), // #1
		common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465"), // #3
		common.HexToAddress("0x6e31e5b68a98dcd17264bd1ba547d0b3e874da1e"), // #5
		common.HexToAddress("0x3a18598184ef84198db90c28fdfdfdf56544f747"), // #4
		common.HexToAddress("0x22a672eab2b1a3ff3ed91563205a56ca5a560e08"), // #6
	}
	devChainConfig = &ChainConfig{
		ChainID: big.NewInt(DevChainId),
		Dpor: &DporConfig{
			Period:                DefaultBlockPeriod,
			TermLen:               4,
			ViewLen:               3,
			ValidatorsLen:         4,
			MaxInitBlockNumber:    120,
			ProxyContractRegister: devProxyContractRegister,
			Contracts:             devContractAddressMap,
			ImpeachTimeout:        time.Second * DefaultBlockPeriod * 2,
		},
	}

	devProposers = []common.Address{
		common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092"),
		common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"),
		common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465"),
		common.HexToAddress("0x6e31e5b68a98dcd17264bd1ba547d0b3e874da1e"),
	}

	devValidators = []common.Address{
		common.HexToAddress("0x7b2f052a372951d02798853e39ee56c895109992"),
		common.HexToAddress("0x2f0176cc3a8617b6ddea6a501028fa4c6fc25ca1"),
		common.HexToAddress("0xe4d51117832e84f1d082e9fc12439b771a57e7b2"),
		common.HexToAddress("0x32bd7c33bb5060a85f361caf20c0bda9075c5d51"),
	}
)
