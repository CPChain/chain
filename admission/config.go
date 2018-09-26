package admission

import (
	"math"
	"time"
)

type workStatus = uint32

const maxNonce = math.MaxUint64

var password = "password"

const (
	// AcIdle status done.
	AcIdle workStatus = iota + 1
	// AcRunning status running.
	AcRunning
)

// Config admission control's configuration.
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
	BlockNumber uint64 `json:"block_number"`
	CPUNonce    uint64 `json:"cpu_nonce"`
	MemoryNonce uint64 `json:"memory_nonce"`
}
