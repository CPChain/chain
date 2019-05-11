package common

import (
	"bitbucket.org/cpchain/chain/configs"
	"github.com/ethereum/go-ethereum/common"
)

// GetContractAddress get contract address by name
func GetContractAddress(name string) common.Address {
	return configs.MainnetContractAddressMap[name]
}
