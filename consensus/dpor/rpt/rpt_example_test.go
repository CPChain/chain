package rpt

import (
	"fmt"

	"github.com/ethereum/go-ethereum/common"
)

func ExampleRPTer_getRpt() {
	hex := "0x96216849c49358B10257cb55b28eA603c874b05E"
	address := common.HexToAddress(hex)

	r := RPTer{}
	rpt := r.getRpt(address)
	fmt.Println("address:", rpt.Address.Hex(), "rpt:", rpt.Rpt)
	// output: address: 0x96216849c49358B10257cb55b28eA603c874b05E rpt: 50
}
