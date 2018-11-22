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
	proxyContractRegisterAddress := deploy.ProxyContractRegister()
	deploy.PrintContract(proxyContractRegisterAddress)

	// 1
	deploy.FormatPrint("1.DeploySignerConnectionRegister")
	signerAddress := deploy.DeploySignerConnectionRegister()
	deploy.PrintContract(signerAddress)

	deploy.RegisterProxyAddress(proxyContractRegisterAddress, signerAddress)

	// 2
	deploy.FormatPrint("2.DeployAdmission")
	admissionAddress := deploy.DeployAdmission()
	deploy.PrintContract(admissionAddress)

	proxyAdmissionAddress := deploy.RegisterProxyAddress(proxyContractRegisterAddress, admissionAddress)

	// 3
	deploy.FormatPrint("3.DeployCampaign")
	campaignAddress := deploy.DeployCampaign(proxyAdmissionAddress)
	deploy.PrintContract(campaignAddress)

	deploy.RegisterProxyAddress(proxyContractRegisterAddress, campaignAddress)

	// 4
	deploy.FormatPrint("4.DeployRpt")
	rptAddress := deploy.DeployRpt()
	deploy.PrintContract(rptAddress)

	deploy.RegisterProxyAddress(proxyContractRegisterAddress, rptAddress)

	// 5
	deploy.FormatPrint("5.DeployRegister")
	registerAddress := deploy.DeployRegister()
	deploy.PrintContract(registerAddress)

	deploy.RegisterProxyAddress(proxyContractRegisterAddress, registerAddress)

	// 6
	deploy.FormatPrint("6.DeployPdash")
	pdashAddress := deploy.DeployPdash()
	deploy.PrintContract(pdashAddress)

	deploy.RegisterProxyAddress(proxyContractRegisterAddress, pdashAddress)
}
