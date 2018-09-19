package main

import (
	"github.com/ethereum/go-ethereum/cmd/smartcontract/deploy"
)

func main() {
	deploy.FormatPrint("DeploySignerConnectionRegister")
	contractAddress := deploy.DeploySignerConnectionRegister()
	deploy.PrintContract(contractAddress)

	deploy.FormatPrint("DeployCampaign")
	contractAddress = deploy.DeployCampaign()
	deploy.PrintContract(contractAddress)
}
