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
	"fmt"
	"os"
	"sync"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/tools/smartcontract/config"
	"bitbucket.org/cpchain/chain/tools/smartcontract/deploy"
	"github.com/ethereum/go-ethereum/common"
)

func main() {
	log.Info("cmdline args", "args", os.Args)
	if len(os.Args) != 4 {
		fmt.Println("Usage: smartcontract <endpoint> <keystore path> <password>")
		return
	}
	config.SetConfig(os.Args[1], os.Args[2])

	password := os.Args[3]
	log.Info("contract deploy node's password", "password", password)

	// deploy init contract
	deploy.FormatPrint("0.DeployProxyContractRegister")
	proxyContractRegisterAddress := deploy.ProxyContractRegister(password)
	deploy.PrintContract(proxyContractRegisterAddress)

	var wg1 sync.WaitGroup

	// 1
	wg1.Add(2)
	go deployProposer(password, proxyContractRegisterAddress, &wg1 /*, 1, 2, 3*/)

	// 2,3
	go deployRewardAdmissionAndCampaign(password, proxyContractRegisterAddress, &wg1 /*, 4, 5, 6, 7, 8, 9*/)
	fmt.Println("======== wait wg1 =========")
	wg1.Wait()

	var wg2 sync.WaitGroup
	wg2.Add(2)
	// 4
	go deployRpt(password, proxyContractRegisterAddress, &wg2 /*, 10, 11, 12*/)

	// 5
	go deployRegister(password, proxyContractRegisterAddress, &wg2 /*, 13, 14, 15*/)
	fmt.Println("======== wait wg2 =========")
	wg2.Wait()

	var wg3 sync.WaitGroup
	wg3.Add(1)
	// 6
	go deployPdash(password, proxyContractRegisterAddress, &wg3 /*, 16, 17, 18*/)

	fmt.Println("======== wait wg3 =========")
	wg3.Wait()

	var wg4 sync.WaitGroup
	wg4.Add(1)
	// 7
	go deployPdashProxy(password, proxyContractRegisterAddress, &wg4 /*,19,20,21*/)
	fmt.Println("======== wait wg4 =========")
	wg4.Wait()
	fmt.Println("======== init contract deploy completed=========")
}

func deployProposer(password string, proxyContractRegisterAddress common.Address, wg *sync.WaitGroup) {
	deploy.FormatPrint("1.DeployProposer")
	signerAddress := deploy.DeployProposerRegister(password, 1)
	deploy.PrintContract(signerAddress)
	deploy.RegisterProxyAddress(proxyContractRegisterAddress, signerAddress, password, 2, 3)
	wg.Done()
}

// TODO: @xmx WILL ADJUST NONCE AND ORDER NUMBERS
func deployRewardAdmissionAndCampaign(password string, proxyContractRegisterAddress common.Address, wg *sync.WaitGroup) {
	// 2
	deploy.FormatPrint("2.DeployReward")
	rewardAddress := deploy.DeployReward(password, 3)
	deploy.PrintContract(rewardAddress)
	proxyRewardAddress := deploy.RegisterProxyAddress(proxyContractRegisterAddress, rewardAddress, password, 13, 14)

	// 3
	deploy.FormatPrint("3.DeployAdmission")
	admissionAddress := deploy.DeployAdmission(password, 4)
	deploy.PrintContract(admissionAddress)
	proxyAdmissionAddress := deploy.RegisterProxyAddress(proxyContractRegisterAddress, admissionAddress, password, 5, 6)
	// 4
	deploy.FormatPrint("4.DeployCampaign")
	campaignAddress := deploy.DeployCampaign(proxyAdmissionAddress, proxyRewardAddress, password, 7)
	deploy.PrintContract(campaignAddress)
	deploy.RegisterProxyAddress(proxyContractRegisterAddress, campaignAddress, password, 8, 9)
	wg.Done()
}

func deployRpt(password string, proxyContractRegisterAddress common.Address, wg *sync.WaitGroup) {
	deploy.FormatPrint("5.DeployRpt")
	rptAddress := deploy.DeployRpt(password, 10)
	deploy.PrintContract(rptAddress)
	deploy.RegisterProxyAddress(proxyContractRegisterAddress, rptAddress, password, 11, 12)
	wg.Done()
}
func deployRegister(password string, proxyContractRegisterAddress common.Address, wg *sync.WaitGroup) {
	deploy.FormatPrint("6.DeployRegister")
	registerAddress := deploy.DeployRegister(password, 13, proxyContractRegisterAddress)
	deploy.PrintContract(registerAddress)
	deploy.RegisterProxyAddress(proxyContractRegisterAddress, registerAddress, password, 14, 15)
	wg.Done()
}

func deployPdash(password string, proxyContractRegisterAddress common.Address, wg *sync.WaitGroup) {
	deploy.FormatPrint("7.DeployPdash")
	pdashAddress := deploy.DeployPdash(password, 16)
	deploy.PrintContract(pdashAddress)
	deploy.RegisterProxyAddress(proxyContractRegisterAddress, pdashAddress, password, 17, 18)
	wg.Done()
}

func deployPdashProxy(password string, proxyContractRegisterAddress common.Address, wg *sync.WaitGroup) {
	deploy.FormatPrint("8.DeployPdashProxy")
	pdashAddress := deploy.DeployPdashProxy(password, 19, proxyContractRegisterAddress)
	deploy.PrintContract(pdashAddress)
	deploy.RegisterProxyAddress(proxyContractRegisterAddress, pdashAddress, password, 20, 21)
	wg.Done()
}
