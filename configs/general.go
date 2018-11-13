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
	CpchainChainId = 42
	TestnetChainId = 43
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
		Ethash:  new(EthashConfig),
	}

	// 	// MainnetChainConfig is the chain parameters to run a node on the CPChain main network.
	MainnetChainConfig = &ChainConfig{
		ChainID: big.NewInt(CpchainChainId),

		Dpor: &DporConfig{
			Period:                1,
			Epoch:                 4,
			View:                  3,
			MaxInitBlockNumber:    96,
			ProxyContractRegister: common.HexToAddress("0x7900dd1d71fc5c57ba56e4b768de3c2264253335"),
			Contracts: map[string]common.Address{
				"campaign": common.HexToAddress("0x1a9fAE75908752d0ABf4DCa45ebcaC311C376290"),
				"signer":   common.HexToAddress("0x4CE687F9dDd42F26ad580f435acD0dE39e8f9c9C"),
				// TODO @hmw make the name more concrete
				"register": common.HexToAddress("3A220f351252089D385b29beca14e27F204c296A"),
			},
		},
	}

	// AllEthashProtocolChanges contains every protocol change (EIPs) introduced
	// and accepted by the Cpchain core developers into the Ethash consensus.
	//
	// This configuration is intentionally not using keyed fields to force anyone
	// adding flags to the config to also have to set these fields.
	AllEthashProtocolChanges = &ChainConfig{
		ChainID: big.NewInt(1337),
		Ethash:  new(EthashConfig),
		Dpor:    nil,
	}

	// FIXME add to genesis.go
	AllCpchainProtocolChanges = &ChainConfig{
		ChainID: big.NewInt(CpchainChainId),
		Ethash:  nil,
		Dpor:    &DporConfig{Period: 1, Epoch: 4},
	}

	// TestChainConfig = &ChainConfig{big.NewInt(1), big.NewInt(0), nil, false, big.NewInt(0), common.Hash{}, big.NewInt(0), big.NewInt(0), big.NewInt(0), nil, new(EthashConfig), nil}
	TestChainConfig = &ChainConfig{big.NewInt(CpchainChainId), nil, &DporConfig{Period: 0, Epoch: 4}}

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
	Ethash *EthashConfig `json:"ethash,omitempty" toml:"ethash,omitempty"`
	Dpor   *DporConfig   `json:"dpor,omitempty" toml:"dpor,omitempty"`
}

// EthashConfig is the consensus engine configs for proof-of-work based sealing.
type EthashConfig struct{}

// String implements the stringer interface, returning the consensus engine details.
func (c *EthashConfig) String() string {
	return "ethash"
}

// DporConfig is the consensus engine configs for proof-of-authority based sealing.
type DporConfig struct {
	Period                uint64                    `json:"period"                toml:"period"` // Number of seconds between blocks to enforce
	Epoch                 uint64                    `json:"epoch"                 toml:"epoch"`  // Epoch length to reset votes and checkpoint
	View                  uint64                    `json:"view"                  toml:"view"`   // View length of blocks one signer can seal in one committee
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
	case c.Ethash != nil:
		engine = c.Ethash
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

	return c.ChainID.Uint64() == CpchainChainId
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
