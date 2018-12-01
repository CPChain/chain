// Copyright 2018 The cphain authors
// Copyright 2016 The go-ethereum Authors

package configs

import (
	"fmt"
	"math/big"
	"time"

	"github.com/ethereum/go-ethereum/common"
)

const (
	Version          = "0.0.1"
	ClientIdentifier = "cpchain" // Client identifier to advertise over the network
)

const (
	DefaultChainId = 41
	MainnetChainId = 42
	TestnetChainId = 43
)

const (
	DefaultBlockPeriod = 1
)

// TODO @hmw make the name more meaningful.  add doc.
const (
	ContractCampaign = "campaign" // address of campaign contract,select rnode
	ContractProposer = "proposer" // address of proposer_register contract, register proposer address in proposer_register contract
	ContractRegister = "register" // address of register contract
	ContractRpt      = "rpt"      // address of rpt contract,Calculation the rpt of rnode
	ContractPdash    = "pdash"    // address of pdash
)

var (
	DefaultCandidates = []common.Address{
		common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"),
		common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092"),
		common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465"),
		common.HexToAddress("0x3a18598184ef84198db90c28fdfdfdf56544f747"),
		common.HexToAddress("0x6e31e5b68a98dcd17264bd1ba547d0b3e874da1e"),
		common.HexToAddress("0x22a672eab2b1a3ff3ed91563205a56ca5a560e08"),
		common.HexToAddress("0x7b2f052a372951d02798853e39ee56c895109992"),
		common.HexToAddress("0x2f0176cc3a8617b6ddea6a501028fa4c6fc25ca1"),
		common.HexToAddress("0xe4d51117832e84f1d082e9fc12439b771a57e7b2"),
		common.HexToAddress("0x32bd7c33bb5060a85f361caf20c0bda9075c5d51"),
	}

	// TODO: @AC define testnet configuration
	TestnetChainConfig = &ChainConfig{
		ChainID: big.NewInt(TestnetChainId),

		Dpor: &DporConfig{
			Period:                1,
			TermLen:               4,
			ViewLen:               3,
			MaxInitBlockNumber:    120,
			ProxyContractRegister: common.HexToAddress("0x1a9fae75908752d0abf4dca45ebcac311c376290"),
			Contracts: map[string]common.Address{
				ContractCampaign: common.HexToAddress("0x0ddf4057eedfb80d58029be49bab09bbc45bc500"),
				ContractProposer: common.HexToAddress("0x310236762f36bf0f69f792bd9fb08b5c679aa3f1"),
				ContractRegister: common.HexToAddress("0x019cc04ff9d88529b9e58ff26bfc53bce060e915"),
				ContractRpt:      common.HexToAddress("0x82104907aa699b2982fc46f38fd8c915d03cdb8d"),
				ContractPdash:    common.HexToAddress("0xaaae743244a7a5116470df8bd398e7d562ae8881"),
			},
		},
	}

	// MainnetChainConfig is the chain parameters to run a node on the cpchain main network.
	MainnetChainConfig = &ChainConfig{
		ChainID: big.NewInt(MainnetChainId),
		Dpor: &DporConfig{
			Period:                DefaultBlockPeriod,
			TermLen:               4,
			ViewLen:               3,
			MaxInitBlockNumber:    120,
			ProxyContractRegister: common.HexToAddress("0x1a9fae75908752d0abf4dca45ebcac311c376290"),
			Contracts: map[string]common.Address{
				ContractCampaign: common.HexToAddress("0x0ddf4057eedfb80d58029be49bab09bbc45bc500"),
				ContractProposer: common.HexToAddress("0x310236762f36bf0f69f792bd9fb08b5c679aa3f1"),
				ContractRegister: common.HexToAddress("0x019cc04ff9d88529b9e58ff26bfc53bce060e915"),
				ContractRpt:      common.HexToAddress("0x82104907aa699b2982fc46f38fd8c915d03cdb8d"),
				ContractPdash:    common.HexToAddress("0xaaae743244a7a5116470df8bd398e7d562ae8881"),
			},
			ImpeachTimeout: time.Second * DefaultBlockPeriod * 2,
		},
	}

	// this contains all the changes we have made to the cpchain protocol.
	// serves as the *default* config.
	DefaultChainConfig = &ChainConfig{
		ChainID: big.NewInt(DefaultChainId),
		Dpor:    &DporConfig{Period: 1, TermLen: 4},
	}

	TestChainConfig = &ChainConfig{big.NewInt(MainnetChainId), &DporConfig{Period: 0, TermLen: 4}}

	TestRules = TestChainConfig.Rules(new(big.Int))
)

// ChainConfig is the core config which determines the blockchain settings.
//
// ChainConfig is stored in the database on a per block basis. This means
// that any network, identified by its genesis block, can have its own
// set of configuration options.
type ChainConfig struct {
	ChainID *big.Int `json:"chainId" toml:"chainId"` // chainId identifies the current chain and is used for replay protection

	// Various consensus engines
	Dpor *DporConfig `json:"dpor,omitempty" toml:"dpor,omitempty"`
}

// DporConfig is the consensus engine configs for proof-of-authority based sealing.
type DporConfig struct {
	Period                uint64                    `json:"period"                toml:"period"`             // Number of seconds between blocks to enforce
	TermLen               uint64                    `json:"termLen"               toml:"termLen"`            // Term length to reset votes and checkpoint
	ViewLen               uint64                    `json:"viewLen"               toml:"viewLen"`            // View length of blocks one signer can seal in one committee
	MaxInitBlockNumber    uint64                    `json:"maxInitBlockNumber"    toml:"maxInitBlockNumber"` // The maximum block number which uses default proposers
	Contracts             map[string]common.Address `json:"contracts"             toml:"contracts"`
	ProxyContractRegister common.Address            `json:"proxyContractRegister" toml:"proxyContractRegister"`
	ImpeachTimeout        time.Duration             `json:"impeachTimeout" toml:"impeachTimeout"`
}

// String implements the stringer interface, returning the consensus engine details.
func (c *DporConfig) String() string {
	return "dpor"
}

// String implements the fmt.Stringer interface.
func (c *ChainConfig) String() string {
	var engine interface{}
	switch {
	case c.Dpor != nil:
		engine = c.Dpor
	default:
		engine = "unknown"
	}
	return fmt.Sprintf("{ChainID: %v Engine: %v}",
		c.ChainID,
		engine,
	)
}

// IsCpchain returns if it is CpchainDawn era.
func (c *ChainConfig) IsCpchain() bool {
	if c.ChainID == nil {
		return false
	}

	return c.ChainID.Uint64() == MainnetChainId
}

// GasTable returns the gas table corresponding to the current phase (homestead or homestead reprice).
//
// The returned GasTable's fields shouldn't, under any circumstances, be changed.
func (c *ChainConfig) GasTable(num *big.Int) GasTable {
	return GasTableCep0
}

// ConfigCompatError is raised if the locally-stored blockchain is initialised with a
// ChainConfig that would alter the past.
type ConfigCompatError struct {
	What string
	// block numbers of the stored and new configurations
	StoredConfig, NewConfig *big.Int
	// the block number to which the local chain must be rewound to correct the error
	RewindTo uint64
}

func (err *ConfigCompatError) Error() string {
	return fmt.Sprintf("mismatching %s in database (have %d, want %d, rewindto %d)", err.What, err.StoredConfig, err.NewConfig, err.RewindTo)
}

// Rules wraps ChainConfig and is merely syntatic sugar or can be used for functions
// that do not have or require information about the block.
//
// Rules is a one time interface meaning that it shouldn't be used in between transition
// phases.
type Rules struct {
	ChainID   *big.Int
	IsCpchain bool
}

// Rules ensures c's ChainID is not nil.
func (c *ChainConfig) Rules(num *big.Int) Rules {
	chainID := c.ChainID
	if chainID == nil {
		chainID = new(big.Int)
	}
	return Rules{ChainID: new(big.Int).Set(chainID), IsCpchain: c.IsCpchain()}
}
