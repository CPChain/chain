// Copyright 2018 The cphain authors
// Copyright 2016 The go-ethereum Authors

package configs

import (
	"fmt"
	"math/big"

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
	ContractCampaign = "campaign"
	ContractSigner   = "signer"
	ContractRegister = "register"
	ContractRpt      = "rpt"
	ContractPdash    = "pdash"
)

// Genesis hashes to enforce below configs on.
var (
	// hash refers to default block.
	MainnetGenesisHash = common.HexToHash("0x6a1455819a218618d870ad9c84257d4917ec6c6e10f4c133004dd1f8a687612a")
)
var (
	// TODO: @AC define testnet configuration
	TestnetChainConfig = &ChainConfig{
		ChainID: big.NewInt(TestnetChainId),
	}

	// MainnetChainConfig is the chain parameters to run a node on the cpchain main network.
	MainnetChainConfig = &ChainConfig{
		ChainID: big.NewInt(MainnetChainId),

		Dpor: &DporConfig{
			Period:                1,
			TermLen:               4,
			ViewLen:               3,
			MaxInitBlockNumber:    96,
			ProxyContractRegister: common.HexToAddress("0x1a9fae75908752d0abf4dca45ebcac311c376290"),
			Contracts: map[string]common.Address{
				ContractCampaign: common.HexToAddress("0x0ddf4057eedfb80d58029be49bab09bbc45bc500"),
				ContractSigner:   common.HexToAddress("0x310236762f36bf0f69f792bd9fb08b5c679aa3f1"),
				ContractRegister: common.HexToAddress("0x019cc04ff9d88529b9e58ff26bfc53bce060e915"),
				ContractRpt:      common.HexToAddress("0x82104907aa699b2982fc46f38fd8c915d03cdb8d"),
				ContractPdash:    common.HexToAddress("0xaaae743244a7a5116470df8bd398e7d562ae8881"),
			},
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
	Period                uint64                    `json:"period"                toml:"period"`  // Number of seconds between blocks to enforce
	TermLen               uint64                    `json:"termLen"               toml:"termLen"` // Term length to reset votes and checkpoint
	ViewLen               uint64                    `json:"viewLen"               toml:"viewLen"` // View length of blocks one signer can seal in one committee
	MaxInitBlockNumber    uint64                    `json:"maxInitBlockNumber"    toml:"maxInitBlockNumber"`
	Contracts             map[string]common.Address `json:"contracts"             toml:"contracts"`
	ProxyContractRegister common.Address            `json:"proxyContractRegister" toml:"proxyContractRegister"`
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
