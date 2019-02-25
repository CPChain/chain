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

var (
	proxyCampaignContractAddress common.Address
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
	title := "[0.DeployProxyContractRegister]"
	proxyContractRegisterAddress := deploy.ProxyContractRegister(password)
	deploy.PrintContract(title, proxyContractRegisterAddress)

	var wg1 sync.WaitGroup

	// 1
	wg1.Add(2)
	go deployProposer(password, proxyContractRegisterAddress, &wg1 /*, 1, 2, 3*/)

	// 2,3
	go deployRewardAdmissionAndCampaign(password, proxyContractRegisterAddress, &wg1 /*, 4, 5, 6, 7, 8, 9,10,11,12*/)
	wg1.Wait()

	var wg2 sync.WaitGroup
	wg2.Add(2)
	// 4
	go deployRpt(password, proxyContractRegisterAddress, &wg2 /*, 13, 14, 15*/)

	// 5
	go deployRegister(password, proxyContractRegisterAddress, &wg2 /*, 16, 17, 18*/)
	wg2.Wait()

	var wg3 sync.WaitGroup
	wg3.Add(1)
	// 6
	go deployPdash(password, proxyContractRegisterAddress, &wg3 /*, 19,20,21*/)
	wg3.Wait()

	var wg4 sync.WaitGroup
	wg4.Add(1)
	// 7
	go deployPdashProxy(password, proxyContractRegisterAddress, &wg4 /*,22,23,24*/)
	wg4.Wait()

	// 8
	deploy.UpdateCampaignParameters(password, proxyCampaignContractAddress, 25, 26)
	fmt.Println("======== init contract deploy completed=========")
}

func deployProposer(password string, proxyContractRegisterAddress common.Address, wg *sync.WaitGroup) {
	title := "[1.DeployProposer]"
	signerAddress := deploy.DeployProposerRegister(password, 1)
	deploy.PrintContract(title, signerAddress)
	deploy.RegisterProxyAddress(title, proxyContractRegisterAddress, signerAddress, password, 2, 3)
	wg.Done()
}

// TODO: @xmx WILL ADJUST NONCE AND ORDER NUMBERS
func deployRewardAdmissionAndCampaign(password string, proxyContractRegisterAddress common.Address, wg *sync.WaitGroup) {
	// 2
	title := "[2.DeployReward]"
	rewardAddress := deploy.DeployReward(password, 4)
	deploy.PrintContract(title, rewardAddress)
	proxyRewardAddress := deploy.RegisterProxyAddress(title, proxyContractRegisterAddress, rewardAddress, password, 5, 6)

	// 3
	title = "[3.DeployAdmission]"
	admissionAddress := deploy.DeployAdmission(password, 7)
	deploy.PrintContract(title, admissionAddress)
	proxyAdmissionAddress := deploy.RegisterProxyAddress(title, proxyContractRegisterAddress, admissionAddress, password, 8, 9)
	// 4
	title = "[4.DeployCampaign]"
	campaignAddress := deploy.DeployCampaign(proxyAdmissionAddress, proxyRewardAddress, password, 10)
	deploy.PrintContract(title, campaignAddress)
	proxyCampaignContractAddress = deploy.RegisterProxyAddress(title, proxyContractRegisterAddress, campaignAddress, password, 11, 12)
	wg.Done()
}

func deployRpt(password string, proxyContractRegisterAddress common.Address, wg *sync.WaitGroup) {
	title := "[5.DeployRpt]"
	rptAddress := deploy.DeployRpt(password, 13)
	deploy.PrintContract(title, rptAddress)
	deploy.RegisterProxyAddress(title, proxyContractRegisterAddress, rptAddress, password, 14, 15)
	wg.Done()
}
func deployRegister(password string, proxyContractRegisterAddress common.Address, wg *sync.WaitGroup) {
	title := "[6.DeployRegister]"
	registerAddress := deploy.DeployRegister(password, 16, proxyContractRegisterAddress)
	deploy.PrintContract(title, registerAddress)
	deploy.RegisterProxyAddress(title, proxyContractRegisterAddress, registerAddress, password, 17, 18)
	wg.Done()
}

func deployPdash(password string, proxyContractRegisterAddress common.Address, wg *sync.WaitGroup) {
	title := "[7.DeployPdash]"
	pdashAddress := deploy.DeployPdash(password, 19)
	deploy.PrintContract(title, pdashAddress)
	deploy.RegisterProxyAddress(title, proxyContractRegisterAddress, pdashAddress, password, 20, 21)
	wg.Done()
}

func deployPdashProxy(password string, proxyContractRegisterAddress common.Address, wg *sync.WaitGroup) {
	title := "[8.DeployPdashProxy]"
	pdashAddress := deploy.DeployPdashProxy(password, 22, proxyContractRegisterAddress)
	deploy.PrintContract(title, pdashAddress)
	deploy.RegisterProxyAddress(title, proxyContractRegisterAddress, pdashAddress, password, 23, 24)
	wg.Done()
}
