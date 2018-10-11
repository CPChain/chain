package main

import (
	"bitbucket.org/cpchain/chain/tools/smartcontract/deploy"
)

func main() {
	deploy.FormatPrint("DeploySignerConnectionRegister")
	contractAddress := deploy.DeploySignerConnectionRegister()
	deploy.PrintContract(contractAddress)

	deploy.FormatPrint("DeployCampaign")
	contractAddress = deploy.DeployCampaign()
	deploy.PrintContract(contractAddress)

	deploy.FormatPrint("DeployCampaignVerify")
	contractAddress = deploy.DeployCampaignVerify()

	deploy.FormatPrint("DeployProxyContractRegister")
	contractAddress = deploy.ProxyContractRegister()
	deploy.PrintContract(contractAddress)
}
