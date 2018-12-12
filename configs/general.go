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
	DevChainId     = 41
	MainnetChainId = 42
	TestnetChainId = 43
)

const (
	DEV     = "dev"
	TESTNET = "testnet"
	MAINNET = "prod"
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
	chainConfigMap = map[string]*ChainConfig{
		DEV:     devChainConfig,
		TESTNET: testnetChainConfig,
		MAINNET: mainnetChainConfig,
	}

	proposersMap = map[string][]common.Address{
		DEV:     devProposers,
		TESTNET: testnetProposers,
		MAINNET: mainnetProposers,
	}

	candidatesMap = map[string][]common.Address{
		DEV:     devDefaultCandidates,
		TESTNET: testnetDefaultCandidates,
		MAINNET: mainnetDefaultCandidates,
	}

	validatorsMap = map[string][]common.Address{
		DEV:     devValidators,
		TESTNET: testnetValidators,
		MAINNET: mainnetValidators,
	}
)

var (
	// just for test
	TestChainConfig = &ChainConfig{big.NewInt(MainnetChainId), &DporConfig{Period: 0, TermLen: 4}}
)

// this contains all the changes we have made to the cpchain protocol.
// serves as the *default* config.
func ChainConfigInfo() *ChainConfig {
	return chainConfigMap[GetRunMode()]
}

func Candidates() []common.Address {
	return candidatesMap[GetRunMode()]
}

func Proposers() []common.Address {
	return proposersMap[GetRunMode()]
}

func Validators() []common.Address {
	return validatorsMap[GetRunMode()]
}

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
