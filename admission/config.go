package admission

import (
	"math"
	"time"
)

type workStatus = uint32

const maxNonce = math.MaxUint64

var numOfCampaign = 10
var myRpt = 60
var keystonePath = "../examples/cpchain/data/dd1/keystore/"

const (
	// AcIdle status done.
	AcIdle workStatus = iota + 1
	// AcRunning status running.
	AcRunning
)

//Config admission control's configuration.
type Config struct {
	// CampaignContractAddress public campaign's contract address.
	// common.HexToAddress("0x1a9fAE75908752d0ABf4DCa45ebcaC311C376290")
	CampaignContractAddress string
	// MemoryDifficulty memory minimum requirements.
	MemoryDifficulty int64
	// CPUDifficulty cpu minimum requirements.
	CPUDifficulty int64
	// MemoryLifeTime memory pow work max time to live.
	MemoryLifeTime time.Duration
	// CPULifeTime cpu pow work max time to live.
	CPULifeTime time.Duration
}

var (
	defaultCPUDifficulty           = int64(55)
	defaultMemoryDifficulty        = int64(55)
	defaultCPULifeTime             = 1 * 60 * time.Second
	defaultMemoryLifeTime          = 1 * 60 * time.Second
	defaultCampaignContractAddress = "0x1a9fAE75908752d0ABf4DCa45ebcaC311C376290"
)

// DefaultConfig default admission config.
var DefaultConfig = Config{
	CampaignContractAddress: defaultCampaignContractAddress,
	CPUDifficulty:           defaultCPUDifficulty,
	MemoryDifficulty:        defaultMemoryDifficulty,
	MemoryLifeTime:          defaultMemoryLifeTime,
	CPULifeTime:             defaultCPULifeTime,
}

// ProofInfo is used to send to contract
type ProofInfo struct {
	CPUProofInfo
	MemoryProofInfo
}

// CPUProofInfo pow result of cpu
type CPUProofInfo struct {
	// Nonce the result of pow
	Nonce uint64 `json:"nonce"`
	// BlockNumber input block number for pow
	BlockNumber uint64 `json:"block_number"`
}

// MemoryProofInfo pow result of memory
type MemoryProofInfo CPUProofInfo
