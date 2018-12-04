package deploy

import (
	"context"
	"fmt"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/commons/log"
	rpt "bitbucket.org/cpchain/chain/contracts/dpor/contracts"
	"bitbucket.org/cpchain/chain/tools/smartcontract/config"
	"github.com/ethereum/go-ethereum/common"
)

func TestRpt(t *testing.T) {
	t.Skip("skip rpt integrate test")

	client, err, _, _, fromAddress := config.Connect()
	ctx := context.Background()
	printBalance(client, fromAddress)

	// addr := common.HexToAddress("0xca53baf44e68a2f440cafee2bbcc23631ad2689e") // real
	addr := common.HexToAddress("0x82104907aa699b2982fc46f38fd8c915d03cdb8d") // proxy
	r, err := rpt.NewRpt(addr, client)

	code, err := client.CodeAt(ctx, addr, nil)
	fmt.Println("****************************************")
	if len(code) > 0 {
		fmt.Println("contract code exist")
	} else {
		fmt.Println("contract code not exist")
	}
	fmt.Println("*****************************************")
	if err != nil {
		println("DeployRpt")
		log.Fatal(err.Error())
	}

	a, err := r.GetRpt(nil, common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d85"), big.NewInt(0))
	if err != nil {
		println("GetRpt", "error:", err)
		log.Fatal(err.Error())
	}
	fmt.Println("rpt is :", a)

	b, err := r.GetRpt(nil, common.HexToAddress("0xE94B7b6C5A0e526A4D97f9768AD6097bdE25c62a"), big.NewInt(0))
	if err != nil {
		println("GetRpt", "error:", err)
		log.Fatal(err.Error())
	}
	fmt.Println("rpt is :", b)

	windowsize, err := r.Window(nil)
	if err != nil {
		log.Fatal("get windowzie is error")
	}
	fmt.Println("winodowsize is:", windowsize.Uint64())
}
