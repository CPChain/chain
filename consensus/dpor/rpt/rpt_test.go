package rpt

import (
	"context"
	"fmt"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/params"

	"github.com/ethereum/go-ethereum/common"
)

var (
	//endpoint = "http://localhost:8501"
	endpoint = "https://rinkeby.infura.io"
	blockNum = uint64(0)
	hex      = "0x96216849c49358B10257cb55b28eA603c874b05E"
)

func TestBasicCollector_GetRpt(t *testing.T) {

	address := common.HexToAddress(hex)

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
		t.Errorf("TestBasicCollector_GetRpt error:%v", err)
	}

	rpt := bc.GetRpt(address, blockNum)
	fmt.Println("address:", rpt.Address.Hex(), "rpt:", rpt.Rpt)
	if hex != rpt.Address.Hex() {
		t.Error("rpt address error")
	}
	// output: address: 0x96216849c49358B10257cb55b28eA603c874b05E rpt: 1.8992704077599994e+19
}

func TestNewBasicCollector(t *testing.T) {
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
	address := common.HexToAddress(hex)
	balance, err := bc.BalanceAt(context.Background(), address, big.NewInt(int64(blockNum)))

	fmt.Println(balance, err)
	// output: 15827253397999997450 <nil>

}

func TestBasicCollector_GetRpts(t *testing.T) {
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
		t.Errorf("TestBasicCollector_GetRpts error:%v", err)
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

func TestBasicCollector_GetRptInfos(t *testing.T) {
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
		t.Errorf("TestBasicCollector_GetRptInfos error:%v", err)
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
