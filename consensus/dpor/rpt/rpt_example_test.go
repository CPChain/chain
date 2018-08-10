package rpt

import (
	"fmt"

	"github.com/ethereum/go-ethereum/common"
)

func ExampleBasicCollector_GetRpt() {
	hex := "0x96216849c49358B10257cb55b28eA603c874b05E"
	address := common.HexToAddress(hex)

	bc := BasicCollector{}
	rpt := bc.GetRpt(address)
	fmt.Println("address:", rpt.Address.Hex(), "rpt:", rpt.Rpt)
	// output: address: 0x96216849c49358B10257cb55b28eA603c874b05E rpt: 50
}

func ExampleBasicCollector_GetRpts() {
	bc := BasicCollector{}
	var addresses []common.Address

	for i := 0; i < 3; i++ {
		addresses = append(
			addresses,
			common.HexToAddress("0x"+fmt.Sprintf("%040x", i)),
		)
	}

	fmt.Printf("rpt of %s is %f \n", addresses[0].Hex(), bc.GetRpts(&addresses)[0].Rpt)
	// output: rpt of 0x0000000000000000000000000000000000000000 is 50.000000
}

func ExampleBasicCollector_GetRptInfos() {
	bc := BasicCollector{}
	var addresses []common.Address

	for i := 0; i < 3; i++ {
		addresses = append(
			addresses,
			common.HexToAddress("0x"+fmt.Sprintf("%040x", i)),
		)
	}

	fmt.Printf("rpt info of %s is\n", addresses[0].Hex())
	fmt.Println(bc.GetRptInfos(&addresses)[addresses[0]])
	// output: rpt info of 0x0000000000000000000000000000000000000000 is
	// {{50 50} {50 50}}
}
