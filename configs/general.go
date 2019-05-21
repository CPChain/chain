// Copyright 2018 The cphain authors
// Copyright 2016 The go-ethereum Authors

package configs

import (
	"fmt"
	"math/big"
	"net"
	"strings"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/ethereum/go-ethereum/common"
)

var Version string

const (
	ClientIdentifier = "cpchain" // Client identifier to advertise over the network
	DatabaseName     = "chaindata"
)

// These are the multipliers for ether denominations.
// Example: To get the wei value of an amount in 'douglas', use
//
//    new(big.Int).Mul(value, big.NewInt(params.Douglas))
//
const (
	Wei      = 1
	Ada      = 1e3
	Babbage  = 1e6
	Shannon  = 1e9
	Szabo    = 1e12
	Finney   = 1e15
	Cpc      = 1e18
	Einstein = 1e21
	Douglas  = 1e42
)

const (
	DevChainId     = 41
	MainnetChainId = 42
	TestnetChainId = 43
)

const (
	MainnetNetworkId = 0
	DevNetworkId     = 1
	TestnetNetworkId = 2
)

const (
	DefaultBlockPeriod = 1e4 //  10000 Millisecond, 10 Second
	TestnetBlockPeriod = 3e3 //  3000 Millisecond, 3 Second
	MainnetBlockPeriod = 1e4 //  10000 Millisecond, 10 Second

	DefaultFaultyValidatorsNumber = 1
	TestnetFaultyValidatorsNumber = 1
	MainnetFaultyValidatorsNumber = 2

	DefaultValidatorsNumber = DefaultFaultyValidatorsNumber*3 + 1
	TestnetValidatorsNumber = TestnetFaultyValidatorsNumber*3 + 1
	MainnetValidatorsNumber = MainnetFaultyValidatorsNumber*3 + 1
)

// MaximumCandidateNumber is the max number of candidates read from campaign contract
const (
	MaximumCandidateNumber = 100
)

const (
	DefaultDevMaxInitBlockNumber     = 216
	DefaultTestnetMaxInitBlockNumber = 240
	DefaultMainnetMaxInitBlockNumber = 216
)

const (
	DefaultWaitTimeBeforeImpeachment    = 2 * time.Minute // wait 120 seconds before first impeachment
	DefaultFailbackTimestampSampleSpace = 2 * time.Minute
)

// DefaultFullSyncPivot is a number that full sync is triggered from it. (head - DefaultFullSyncPivot)
const (
	DefaultFullSyncPivot = 1024
)

const (
	DefaultGasLimitPerBlock = 100000000
)

// TODO @hmw make the name more meaningful.  add doc.
const (
	ContractCampaign   = "campaign"   // address of campaign contract,select rnode
	ContractProposer   = "proposer"   // address of proposer_register contract, register proposer address in proposer_register contract
	ContractReward     = "reward"     // address of reward contract
	ContractRegister   = "register"   // address of register contract
	ContractRpt        = "rpt"        // address of rpt contract,Calculation the rpt of rnode
	ContractPdash      = "pdash"      // address of pdash
	ContractAdmission  = "admission"  // address of admission
	ContractPdashProxy = "pdashProxy" // address of PdashProxy
	ContractRnode      = "rnode"      // address of rnode
	ContractCampaign2  = "campaign2"  // address of campaign2
	ContractCampaign3  = "campaign3"  // address of campaign3
	ContractCampaign4  = "campaign4"  // address of campaign4
	ContractRnode2     = "rnode2"     // address of rnode2
	ContractRpt2       = "rpt2"       // address of rpt2 contract,Calculation the rpt of rnode
)

const (
	RNodeMinFundReq = 200000 // 200000 CPC for becoming a RNode
)

// some version numbers
const (
	RnodeVersion    = 1
	CampaignVersion = 1
)

// pivot blocks numbers
const (
	RptCalcMethod2BlockNumber = 343000
	RptCalcMethod3BlockNumber = 372400
	RptCalcMethod4BlockNumber = 390500
	RptCalcMethod5BlockNumber = 398000
	RptCalcMethod6BlockNumber = 454580

	Campaign2BlockNumber = 371900
	Campaign3BlockNumber = 390500
	Campaign4BlockNumber = 454580

	Election2BlockNumber = 454580
)

var (
	chainConfigMap = map[RunMode]*ChainConfig{
		Dev:      devChainConfig,
		Testnet:  testnetChainConfig,
		Mainnet:  mainnetChainConfig,
		Testcase: devChainConfig,
	}

	proposersMap = map[RunMode][]common.Address{
		Dev:      devProposers,
		Testnet:  testnetProposers,
		Mainnet:  mainnetProposers,
		Testcase: devProposers,
	}

	candidatesMap = map[RunMode][]common.Address{
		Dev:      devDefaultCandidates,
		Testnet:  testnetDefaultCandidates,
		Mainnet:  mainnetDefaultCandidates,
		Testcase: devDefaultCandidates,
	}

	validatorsMap = map[RunMode][]common.Address{
		Dev:      devValidators,
		Testnet:  testnetValidators,
		Mainnet:  mainnetValidators,
		Testcase: devValidators,
	}
)

var (
	// just for test
	TestChainConfig = &ChainConfig{big.NewInt(DevChainId), &DporConfig{Period: 0, TermLen: 4}}
)

// this contains all the changes we have made to the cpchain protocol.
// serves as the *default* config.
func ChainConfigInfo() *ChainConfig {
	runModeValue := GetRunMode()
	chainConfig, ok := chainConfigMap[runModeValue]
	if !ok {
		log.Fatal("get chainConfig failed", "runModeValue", runModeValue)
	}
	return chainConfig
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

func Bootnodes() []string {
	switch {
	case IsDev():
		return devBootnodes
	case IsTestnet():
		return testnetBootnodes
	case IsMainnet():
		return mainnetBootnodes
	case IsTestcase():
		return devBootnodes
	default:
		return devBootnodes
	}
}

// Deposit per time when campaign
var (
	depositMap = map[RunMode]*big.Int{
		Dev:      devDeposit,
		Testnet:  testnetDeposit,
		Mainnet:  mainnetDeposit,
		Testcase: devDeposit,
	}
)

func Deposit() *big.Int {
	return depositMap[GetRunMode()]
}

// validator nodes info
var defaultValidatorNodes []string

func GetDefaultValidators() []string {
	return defaultValidatorNodes
}

func InitDefaultValidators(validators []string) {
	defaultValidatorNodes = defaultDevValidatorNodes
	runMode := GetRunMode()
	switch runMode {
	case Mainnet:
		defaultValidatorNodes = defaultMainnetValidatorNodes
	case Testnet:
		defaultValidatorNodes = defaultTestnetValidatorNodes
	case Dev:
		defaultValidatorNodes = defaultDevValidatorNodes
	case Testcase:
		defaultValidatorNodes = defaultDevValidatorNodes
	}

	if validators != nil && len(validators) > 0 {
		defaultValidatorNodes = validators
	}
	convertedValidatorNodes, err := ConvertNodeURL(defaultValidatorNodes)
	if err != nil {
		log.Fatal("convertValidators failed", "error", err)
	}
	log.Info("init validators", "nodes", convertedValidatorNodes)

	defaultValidatorNodes = convertedValidatorNodes
}

func ConvertNodeURL(nodeURLs []string) ([]string, error) {
	validatorNodes := []string{}
	// if domain in nodeId, convert domain to ip and return
	for _, nodeURL := range nodeURLs {
		ipAddress, err := convertDomainNode(nodeURL)
		log.Debug("convertDomainNode", "nodeURL", nodeURL, "ip", ipAddress)
		if err != nil {
			log.Error("error when resolve nodeURL", "error", err)
			return nil, err
		}
		validatorNodes = append(validatorNodes, ipAddress)
	}
	return validatorNodes, nil
}

func convertDomainNode(validator string) (string, error) {
	// get nodeid and ip|host:port
	nodeIdAndAddress := strings.Split(validator, "@")
	host, port, err := net.SplitHostPort(nodeIdAndAddress[1])
	if err != nil {
		return "", fmt.Errorf("invalid host: %v,validator:%v", err, nodeIdAndAddress)
	}
	ipAddress, err := resolveDomain(host)
	if err != nil {
		return "", err
	}
	return nodeIdAndAddress[0] + "@" + ipAddress + ":" + port, nil
}

func resolveDomain(hostname string) (string, error) {
	ipAddress := net.ParseIP(hostname)
	log.Debug("parse ip", "hostname", hostname, "ipAddress", ipAddress)
	if ipAddress != nil {
		return ipAddress.String(), nil
	}
	addr, err := net.LookupHost(hostname)
	if err != nil {
		log.Error("lookup host error", "hostname", hostname, "err", err)
		return "", err
	}
	if len(addr) > 0 {
		return addr[0], nil
	}
	return "", fmt.Errorf("invalid host: %v", err)
}

func ResolveUrl(url string) (string, error) {
	host, port, err := net.SplitHostPort(url[7:])
	ip, err := resolveDomain(host)
	if err != nil {
		log.Fatal("unknown endpoint", "endpoint", url, "err", err)
		return "", err
	}
	return "http://" + ip + ":" + port, err
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
	FaultyNumber          uint64                    `json:"faultyNumber"          toml:"faultyNumber"`       // Number of faulty validators in validator committee
	MaxInitBlockNumber    uint64                    `json:"maxInitBlockNumber"    toml:"maxInitBlockNumber"` // The maximum block number which uses default proposers
	Contracts             map[string]common.Address `json:"contracts"             toml:"contracts"`
	ProxyContractRegister common.Address            `json:"proxyContractRegister" toml:"proxyContractRegister"`
	ImpeachTimeout        time.Duration             `json:"impeachTimeout" toml:"impeachTimeout"`
}

// String implements the stringer interface, returning the consensus engine details.
func (c *DporConfig) String() string {
	return "dpor"
}

func (c *DporConfig) ValidatorsLen() uint64 {
	if c != nil {
		return c.FaultyNumber*3 + 1
	}
	return 0
}

func (c *DporConfig) Certificate(n uint64) bool {
	if c != nil {
		return n >= c.FaultyNumber*2+1
	}
	return false
}

func (c *DporConfig) ImpeachCertificate(n uint64) bool {
	if c != nil {
		return n >= c.FaultyNumber+1
	}
	return false
}

func (c *DporConfig) PeriodDuration() time.Duration {
	if c != nil {
		return time.Duration(int64(c.Period) * int64(time.Millisecond))
	}
	return time.Duration(0)
}

func (c *DporConfig) BlockDelay() time.Duration {
	if c != nil {
		return c.ImpeachTimeout * 1 / 4
	}
	return time.Duration(0)
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
	// add this GasTable, so that in testcase run mode,we can reuse vm tests in https://github.com/ethereum/tests
	if IsTestcase() {
		return GasTableHomestead
	}
	return GasTableCep1
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
