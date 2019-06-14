package common

import (
	"bitbucket.org/cpchain/chain/configs"
	"github.com/ethereum/go-ethereum/common"
)

// GetContractAddress get contract address by name
func GetContractAddress(name string, runMode configs.RunMode) common.Address {
	switch runMode {
	case configs.Mainnet:
		return configs.MainnetContractAddressMap[name]
	case configs.Dev:
		return configs.DevContractAddressMap[name]
	case configs.TestMainnet:
		return configs.TestMainnetContractAddressMap[name]
	case configs.Testnet:
		return configs.TestnetContractAddressMap[name]
	default:
		return configs.MainnetContractAddressMap[name]
	}
}
