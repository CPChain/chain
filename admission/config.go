package admission

import (
	"math"
	"time"
)

type workStatus = uint32

const maxNonce = math.MaxUint64

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
	// Desposit to motage
	Desposit int64
	// MinimumRpt minimum rpt
	MinimumRpt int64
	// NumberOfCampaign wants to campaign times
	NumberOfCampaignTimes int64
}

var (
	defaultCPUDifficulty           = int64(55)
	defaultMemoryDifficulty        = int64(55)
	defaultCPULifeTime             = 1 * 60 * time.Second
	defaultMemoryLifeTime          = 1 * 60 * time.Second
	defaultCampaignContractAddress = "0x1a9fAE75908752d0ABf4DCa45ebcaC311C376290"
	defaultDesposit                = int64(50)
	defaultMinimumRpt              = int64(50)
	defaultNumberOfCampaignTimes   = int64(1)
)

// DefaultConfig default admission config.
var DefaultConfig = Config{
	CampaignContractAddress: defaultCampaignContractAddress,
	CPUDifficulty:           defaultCPUDifficulty,
	MemoryDifficulty:        defaultMemoryDifficulty,
	MemoryLifeTime:          defaultMemoryLifeTime,
	CPULifeTime:             defaultCPULifeTime,
	Desposit:                defaultDesposit,
	MinimumRpt:              defaultMinimumRpt,
	NumberOfCampaignTimes:   defaultNumberOfCampaignTimes,
}

// ProofInfo is used to send to contract
type ProofInfo struct {
	BlockNumber uint64 `json:"block_number"`
	CPUNonce    uint64 `json:"cpu_nonce"`
	MemoryNonce uint64 `json:"memory_nonce"`
}
