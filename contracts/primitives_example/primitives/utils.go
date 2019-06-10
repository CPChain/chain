package primitives

import (
	"errors"
	"math/big"
	"time"

	"github.com/ethereum/go-ethereum/common"
)

var (
	errWrongInput = errors.New("input's length must be 64 bytes")
)

type fakeConfigs struct {
	ContractPdashProxy string
	ContractRegister   string
	ContractCampaign   string
	GetRankGas         uint64
	GetMaintenanceGas  uint64
	IsProxyGas         uint64
	GetTxVolumeGas     uint64
	GetUploadRewardGas uint64
	CpuPowValidateGas  uint64
	MemPowValidateGas  uint64
}

type fakeChainConfig struct {
	Dpor    *fakeDporConfig
	ChainID *big.Int
}

type fakeDporConfig struct {
	Period                uint64
	TermLen               uint64
	ViewLen               uint64
	FaultyNumber          uint64
	MaxInitBlockNumber    uint64
	Contracts             map[string]common.Address
	ProxyContractRegister common.Address
	ImpeachTimeout        time.Duration
}

func (fc *fakeConfigs) ChainConfigInfo() *fakeChainConfig {
	return nil
}

var (
	configs = fakeConfigs{}
)

// extractRptPrimitivesArgs extracts arguments from input byte slice
func extractRptPrimitivesArgs(input []byte) (common.Address, uint64, error) {
	if len(input) != 64 {
		return common.Address{}, 0, errWrongInput
	}

	return common.BytesToAddress(input[12:32]), new(big.Int).SetBytes(input[32:64]).Uint64(), nil
}
