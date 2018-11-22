package deploy

import (
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	rpt "bitbucket.org/cpchain/chain/contracts/dpor/contracts"
	"bitbucket.org/cpchain/chain/tools/smartcontract/config"
	"context"
	"fmt"
	"github.com/ethereum/go-ethereum/common"
	"math/big"
	"testing"
)

func TestRpt(t *testing.T) {
	FormatPrint("DeploySignerConnectionRegister")
	contractAddress := DeploySignerConnectionRegister()
	PrintContract(contractAddress)

	//FormatPrint("DeployCampaignVerify")
	//contractAddress = DeployCampaignVerify()
	//PrintContract(contractAddress)

	FormatPrint("DeployCampaign")
	contractAddress = DeployCampaign(contractAddress)
	PrintContract(contractAddress)

	FormatPrint("DeployRegister")
	contractAddress = DeployRegister()
	PrintContract(contractAddress)

	FormatPrint("DeployPdash")
	contractAddress = DeployPdash()
	PrintContract(contractAddress)

	client, err, privateKey, _, fromAddress := config.Connect()
	ctx := context.Background()
	printBalance(client, fromAddress)
	// Launch contract deploy transaction.
	auth := bind.NewKeyedTransactor(privateKey)
	_, tx, rpt, err := rpt.DeployRpt(auth, client)
	receipt, err := bind.WaitMined(ctx, client, tx)
	code, err := client.CodeAt(ctx, receipt.ContractAddress, nil)
	fmt.Println("****************************************")
	fmt.Println("code:", code)
	fmt.Println("*****************************************")
	if err != nil {
		println("DeployRpt")
		log.Fatal(err.Error())
	}

	a, err := rpt.GetRpt(nil, common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d85"), big.NewInt(0))
	if err != nil {
		println("GetRpt", "error:", err)
		log.Fatal(err.Error())
	}
	fmt.Println("rpt is :", a)

}
