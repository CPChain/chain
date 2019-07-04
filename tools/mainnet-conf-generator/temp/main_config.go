package temp

var Config_mainnet = `
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
		ContractRpt:       common.HexToAddress("{{$.ContractRpt -}}"),
		ContractRnode:     common.HexToAddress("{{$.ContractRnode -}}"),
		ContractAdmission: common.HexToAddress("{{$.ContractAdmission -}}"),
		ContractCampaign:  common.HexToAddress("{{$.ContractCampaign -}}"),
		ContractNetwork:   common.HexToAddress("{{$.ContractNetwork -}}"),
	}

	// config
	mainnetDefaultCandidates = []common.Address{
		common.HexToAddress("{{$.P1 -}}"), // #1
		common.HexToAddress("{{$.P2 -}}"), // #2
		common.HexToAddress("{{$.P3 -}}"), // #3
		common.HexToAddress("{{$.P4 -}}"), // #4
		common.HexToAddress("{{$.P5 -}}"), // #5
		common.HexToAddress("{{$.P6 -}}"), // #6
		common.HexToAddress("{{$.P14 -}}"), // #14
		common.HexToAddress("{{$.P15 -}}"), // #15
		common.HexToAddress("{{$.P16 -}}"), // #16
		common.HexToAddress("{{$.P17 -}}"), // #17
		common.HexToAddress("{{$.P18 -}}"), // #18
		common.HexToAddress("{{$.P19 -}}"), // #19
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
		common.HexToAddress("{{$.V7 -}}"), //#7
		common.HexToAddress("{{$.V8 -}}"), //#8
		common.HexToAddress("{{$.V9 -}}"), //#9
		common.HexToAddress("{{$.V10 -}}"), //#10
		common.HexToAddress("{{$.V11 -}}"), // #11
		common.HexToAddress("{{$.V12 -}}"), // #12
		common.HexToAddress("{{$.V13 -}}"), // #13
	}

	mainnetBootnodes = []string{
		"enode://{{$.B1 -}}@b01.mainnet.cpc-servers.com:30310",
		"enode://{{$.B2 -}}@b02.mainnet.cpc-servers.com:30310",
		"enode://{{$.B3 -}}@b03.mainnet.cpc-servers.com:30310",
	}

	defaultMainnetValidatorNodes = []string{
		"enode://{{$.Ve1 -}}@v01.mainnet.cpc-servers.com:30310",
		"enode://{{$.Ve2 -}}@v02.mainnet.cpc-servers.com:30310",
		"enode://{{$.Ve3 -}}@v03.mainnet.cpc-servers.com:30310",
		"enode://{{$.Ve4 -}}@v04.mainnet.cpc-servers.com:30310",
		"enode://{{$.Ve5 -}}@v05.mainnet.cpc-servers.com:30310",
		"enode://{{$.Ve6 -}}@v06.mainnet.cpc-servers.com:30310",
		"enode://{{$.Ve7 -}}@v07.mainnet.cpc-servers.com:30310",
	}
)
`

type MainnetConfig struct {
	ContractRpt       string
	ContractRnode     string
	ContractAdmission string
	ContractCampaign  string
	ContractNetwork   string

	Ca string

	P1  string
	P2  string
	P3  string
	P4  string
	P5  string
	P6  string
	P14 string
	P15 string
	P16 string
	P17 string
	P18 string
	P19 string

	V7  string
	V8  string
	V9  string
	V10 string
	V11 string
	V12 string
	V13 string

	B1 string
	B2 string
	B3 string

	Ve1 string
	Ve2 string
	Ve3 string
	Ve4 string
	Ve5 string
	Ve6 string
	Ve7 string
}
