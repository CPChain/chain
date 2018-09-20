package main

import (
	"bitbucket.org/cpchain/chain/cmd/smartcontract/deploy"
)

func main() {
	deploy.FormatPrint("DeploySignerConnectionRegister")
	contractAddress := deploy.DeploySignerConnectionRegister()
	deploy.PrintContract(contractAddress)

	deploy.FormatPrint("DeployCampaign")
	contractAddress = deploy.DeployCampaign()
	deploy.PrintContract(contractAddress)
}
