package rpt

import (
	"github.com/ethereum/go-ethereum/common"
)

type OrderInfo struct {
	DescHsah     float64
	ProxyAddress common.Address
	State        State
	Blocknumber  uint64
}

type State struct {
	Creat           bool
	SellerConfirmed bool
	ProxyFetched    bool
	ProxyDelivered  bool
	BuyerConfirmed  bool
	Finished        bool
	SellerRated     bool
	BuyerRatedb     bool
	Disputedb       bool
	Withdrawn       bool
}

var OrderMap map[int]OrderInfo

//type Odermap map[int]OrderInfo

func SetFakeOderInfo() {
	OrderMap = make(map[int]OrderInfo)
	OrderMap[1] = OrderInfo{
		ProxyAddress: common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"),
		State: State{
			Finished: true,
		},
		Blocknumber: 1,
	}
	OrderMap[2] = OrderInfo{
		ProxyAddress: common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"),
		State: State{
			Finished: true,
		},
		Blocknumber: 1,
	}
	OrderMap[3] = OrderInfo{
		ProxyAddress: common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d85"),
		State: State{
			Finished: true,
		},
		Blocknumber: 1,
	}
	OrderMap[4] = OrderInfo{
		ProxyAddress: common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d84"),
		State: State{
			Finished: true,
		},
		Blocknumber: 1,
	}
	OrderMap[5] = OrderInfo{
		ProxyAddress: common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d83"),
		State: State{
			Finished: true,
		},
		Blocknumber: 1,
	}
}
