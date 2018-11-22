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
	// deploy init contract
	deploy.FormatPrint("0.DeployProxyContractRegister")
	proxyAddress := deploy.ProxyContractRegister()
	deploy.PrintContract(proxyAddress)

	deploy.FormatPrint("1.DeploySignerConnectionRegister")
	signerAddress := deploy.DeploySignerConnectionRegister()
	deploy.PrintContract(signerAddress)

	deploy.FormatPrint("2.DeployAdmission")
	admissionAddress := deploy.DeployAdmission()
	deploy.PrintContract(admissionAddress)

	deploy.FormatPrint("3.DeployCampaign")
	campaignAddress := deploy.DeployCampaign(admissionAddress)
	deploy.PrintContract(campaignAddress)

	deploy.FormatPrint("4.DeployRpt")
	rptAddress := deploy.DeployRpt()
	deploy.PrintContract(rptAddress)

	deploy.FormatPrint("5.DeployRegister")
	registerAddress := deploy.DeployRegister()
	deploy.PrintContract(registerAddress)

	deploy.FormatPrint("6.DeployPdash")
	pdashAddress := deploy.DeployPdash()
	deploy.PrintContract(pdashAddress)

	// register real biz contract on proxy contract
	// 1.deploy proxy contract for SignerConnectionRegister && register
	deploy.FormatPrint("1.1 register SignerConnectionRegister")
	proxyForSignerConnectionRegister := deploy.DeployProxy()
	deploy.PrintContract(proxyForSignerConnectionRegister)
	deploy.RegisterProxyAddress(proxyAddress, proxyForSignerConnectionRegister, signerAddress)

	// 2.deploy proxy contract for Admission && register

	// 3.deploy proxy contract for Campaign && register

	// 4.deploy proxy contract for Rpt && register

	// 5.deploy proxy contract for Register && register

	// 6.deploy proxy contract for Pdash && register

}
