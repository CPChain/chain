package main

import (
	"fmt"
	"math/big"
	"os"
	"strconv"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/contracts/dpor/admission"
	"bitbucket.org/cpchain/chain/tools/smartcontract/config"
)

func main() {
	fmt.Println("need 5 args cpuDifficulty cpuWorkTimeout memoryDifficulty memoryWorkTimeout password")
	if len(os.Args) < 6 {
		fmt.Println("Error! need 5 args cpuDifficulty cpuWorkTimeout memoryDifficulty memoryWorkTimeout password")
		return
	}
	password := os.Args[5]
	fmt.Println("cpuDifficulty :", os.Args[1])
	fmt.Println("cpuWorkTimeout :", os.Args[2])
	fmt.Println("memoryDifficulty :", os.Args[3])
	fmt.Println("memoryWorkTimeout :", os.Args[4])

	client, err, privateKey, _, _ := config.Connect(password)
	if err != nil {
		fmt.Println("failed")
		log.Fatal(err.Error(), "error is ", err)
	}

	acAddr := configs.ChainConfigInfo().Dpor.Contracts[configs.ContractCampaign]
	transactOpts := bind.NewKeyedTransactor(privateKey)
	instance, err := admission.NewAdmission(acAddr, client)

	cpuDifficulty, err := strconv.ParseInt(os.Args[1], 10, 64)
	if err != nil {
		fmt.Println("get cpuDifficulty error", err)
	}
	cpuWorkTimeout, err := strconv.ParseInt(os.Args[2], 10, 64)
	if err != nil {
		fmt.Println("get cpuWorkTimeout error", err)
	}
	memoryDifficulty, err := strconv.ParseInt(os.Args[3], 10, 64)
	if err != nil {
		fmt.Println("get memoryDifficulty error", err)
	}
	memoryWorkTimeout, err := strconv.ParseInt(os.Args[4], 10, 64)
	if err != nil {
		fmt.Println("get memoryDifficulty error", err)
	}
	_, err = instance.UpdateCPUDifficulty(transactOpts, big.NewInt(cpuDifficulty))
	if err != nil {
		fmt.Println("UpdateCPUDifficulty is error")
	}
	_, err = instance.UpdateCPUWorkTimeout(transactOpts, big.NewInt(cpuWorkTimeout))
	if err != nil {
		fmt.Println("UpdateCPUWorkTimeout is error")
	}

	_, err = instance.UpdateMemoryDifficulty(transactOpts, big.NewInt(memoryDifficulty))
	if err != nil {
		fmt.Println("UpdateCPUDifficulty is error")
	}

	_, err = instance.UpdateMemoryWorkTimeout(transactOpts, big.NewInt(memoryWorkTimeout))
	if err != nil {
		fmt.Println("UpdateCPUDifficulty is error")
	}

	// get latest nonce

}
