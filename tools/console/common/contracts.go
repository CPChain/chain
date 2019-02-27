package common

import "github.com/ethereum/go-ethereum/common"

// ContractProposer name
var ContractProposer = "proposer"

// ContractReward name
var ContractReward = "reward"

// ContractAdmission name
var ContractAdmission = "admission"

// ContractCampaign name
var ContractCampaign = "campaign"

// ContractRpt name
var ContractRpt = "rpt"

// ContractRegister name
var ContractRegister = "register"

// ContractPdash name
var ContractPdash = "pdash"

// ContractPdashProxy name
var ContractPdashProxy = "pdash_proxy"

// ContractAddressMap map
var ContractAddressMap = map[string]common.Address{
	ContractProposer:   common.HexToAddress("0xf26B6864749cdE85a29afEa57FfeaE115B24b505"),
	ContractReward:     common.HexToAddress("0x94576e35a55D6BbF9bB45120bC835a668557eF42"),
	ContractAdmission:  common.HexToAddress("0x8f01875F462CBBc956CB9C0392dE6053A31C9C99"),
	ContractCampaign:   common.HexToAddress("0x1404Bf355428523F8e51E68Df00A0521e413F98E"),
	ContractRpt:        common.HexToAddress("0x878a9A4155E8D60fbe07074a9061a0Dcc031c212"),
	ContractRegister:   common.HexToAddress("0xA14842fBFfFe76d34e6D45ba5701ec9971bFd596"),
	ContractPdash:      common.HexToAddress("0x3863551C32F18c7454482E718828A1ede00034d6"),
	ContractPdashProxy: common.HexToAddress("0xEfc4282385932d3119FbEcF9d56f4aEed87B3805"),
}

// GetContractAddress get contract address by name
func GetContractAddress(name string) common.Address {
	return ContractAddressMap[name]
}
