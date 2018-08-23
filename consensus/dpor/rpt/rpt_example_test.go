package rpt

import (
	"context"
	"fmt"
	"math/big"

	"github.com/ethereum/go-ethereum/params"

	"github.com/ethereum/go-ethereum/common"
)

func ExampleBasicCollector_GetRpt() {
	hex := "0x96216849c49358B10257cb55b28eA603c874b05E"
	address := common.HexToAddress(hex)
	blockNum := uint64(2764854)
	endpoint := "https://rinkeby.infura.io"
	config := &CollectorConfig{
		LeaderReward: 50,
		ProxyReward:  50,
		UploadReward: 50,
		WindowSize:   5,
		Alpha:        0.2,
		Beta:         0.2,
		Gamma:        0.2,
		Phi:          0.2,
		Omega:        0.2,
		ChainConfig: &params.ChainConfig{
			ChainID: big.NewInt(4),
		},
		DporConfig: &params.DporConfig{
			Epoch:  3,
			Period: 1,
		},
	}
	bc, err := NewBasicCollector(endpoint, config)
	if err != nil {
		fmt.Println(err)
	}

	rpt := bc.GetRpt(address, blockNum)
	fmt.Println("address:", rpt.Address.Hex(), "rpt:", rpt.Rpt)
	// output: address: 0x96216849c49358B10257cb55b28eA603c874b05E rpt: 1.8992704077599994e+19
}

func ExampleNewBasicCollector() {
	endpoint := "https://rinkeby.infura.io"
	config := &CollectorConfig{
		LeaderReward: 50,
		ProxyReward:  50,
		UploadReward: 50,
		Alpha:        0.2,
		Beta:         0.2,
		Gamma:        0.2,
		Phi:          0.2,
		Omega:        0.2,
		WindowSize:   5,
		ChainConfig: &params.ChainConfig{
			ChainID: big.NewInt(4),
		},
		DporConfig: &params.DporConfig{
			Epoch:  3,
			Period: 1,
		},
	}

	bc, err := NewBasicCollector(endpoint, config)
	if err != nil {
		fmt.Println(err)
	}
	hex := "0x96216849c49358B10257cb55b28eA603c874b05E"
	blockNum := 2764854
	address := common.HexToAddress(hex)
	balance, err := bc.BalanceAt(context.Background(), address, big.NewInt(int64(blockNum)))

	fmt.Println(balance, err)
	// output: 15827253397999997450 <nil>

}

func ExampleBasicCollector_GetRpts() {
	blockNum := uint64(2764854)
	endpoint := "https://rinkeby.infura.io"
	config := &CollectorConfig{
		LeaderReward: 50,
		ProxyReward:  50,
		UploadReward: 50,
		Alpha:        0.2,
		Beta:         0.2,
		Gamma:        0.2,
		Phi:          0.2,
		Omega:        0.2,
		WindowSize:   5,
		ChainConfig: &params.ChainConfig{
			ChainID: big.NewInt(4),
		},
		DporConfig: &params.DporConfig{
			Epoch:  3,
			Period: 1,
		},
	}

	bc, err := NewBasicCollector(endpoint, config)
	if err != nil {
		fmt.Println(err)
	}

	var addresses []common.Address

	for i := 0; i < 3; i++ {
		addresses = append(
			addresses,
			common.HexToAddress("0x"+fmt.Sprintf("%040x", i)),
		)
	}

	fmt.Printf("rpt of %s is %f \n", addresses[0].Hex(), bc.GetRpts(&addresses, blockNum)[0].Rpt)
	// output: rpt of 0x0000000000000000000000000000000000000000 is 13766293544625745920.000000
}

func ExampleBasicCollector_GetRptInfos() {
	blockNum := uint64(2764854)
	endpoint := "https://rinkeby.infura.io"
	config := &CollectorConfig{
		LeaderReward: 50,
		ProxyReward:  50,
		UploadReward: 50,
		Alpha:        0.2,
		Beta:         0.2,
		Gamma:        0.2,
		Phi:          0.2,
		Omega:        0.2,
		WindowSize:   5,
		ChainConfig: &params.ChainConfig{
			ChainID: big.NewInt(4),
		},
		DporConfig: &params.DporConfig{
			Epoch:  3,
			Period: 1,
		},
	}

	bc, err := NewBasicCollector(endpoint, config)
	if err != nil {
		fmt.Println(err)
	}
	var addresses []common.Address

	for i := 0; i < 3; i++ {
		addresses = append(
			addresses,
			common.HexToAddress("0x"+fmt.Sprintf("%040x", i)),
		)
	}

	fmt.Printf("rpt info of %s is\n", addresses[0].Hex())
	fmt.Println(bc.GetRptInfos(&addresses, blockNum)[addresses[0]])
	// output: rpt info of 0x0000000000000000000000000000000000000000 is
	// {0 {6.8831467723128726e+19 0 0} {300 300}}
}
