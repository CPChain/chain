// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package main

import (
	"bitbucket.org/cpchain/chain/tools/smartcontract/deploy"
)

func main() {
	deploy.FormatPrint("DeploySignerConnectionRegister")
	contractAddress := deploy.DeploySignerConnectionRegister()
	deploy.PrintContract(contractAddress)

	deploy.FormatPrint("DeployCampaignVerify")
	contractAddress = deploy.DeployCampaignVerify()
	deploy.PrintContract(contractAddress)

	deploy.FormatPrint("DeployCampaign")
	contractAddress = deploy.DeployCampaign(contractAddress)
	deploy.PrintContract(contractAddress)

	deploy.FormatPrint("DeployProxyContractRegister")
	contractAddress = deploy.ProxyContractRegister()
	deploy.PrintContract(contractAddress)

	deploy.FormatPrint("DeployRpt")
	contractAddress = deploy.DeployRpt()
	deploy.PrintContract(contractAddress)

	deploy.FormatPrint("DeployRegister")
	contractAddress = deploy.DeployRegister()
	deploy.PrintContract(contractAddress)

	deploy.FormatPrint("DeployPdash")
	contractAddress = deploy.DeployPdash()
	deploy.PrintContract(contractAddress)
}
