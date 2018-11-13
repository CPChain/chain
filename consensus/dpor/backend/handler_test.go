package backend

import (
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// launch the chain
// new a committee_network_handler
// build the network.

func TestNewHandler(t *testing.T) {
	type args struct {
		config    *configs.DporConfig
		etherbase common.Address
	}

	//define the parameter "config" of NewHandler()
	var testConfig *configs.DporConfig
	testConfig = &configs.DporConfig{
		Period:             1,
		Epoch:              4,
		View:               1,
		MaxInitBlockNumber: 12,
		Contracts: map[string]common.Address{
			"campaign": common.HexToAddress("0x1a9fAE75908752d0ABf4DCa45ebcaC311C376290"),
			"signer":   common.HexToAddress("0x4CE687F9dDd42F26ad580f435acD0dE39e8f9c9C"),
		},
		ProxyContractRegister: common.HexToAddress("0x7900dd1d71fc5c57ba56e4b768de3c2264253335"),
	}
	//define the parameter "etherbase" for NewHandler()
	testEtherbase := common.HexToAddress("0x4CE687F9dDd42F26ad580f435acD0dE39e8f0000")

	//Assign an expected handler
	var expectedResult Handler
	expectedResult.ownAddress = testEtherbase
	expectedResult.contractAddress = common.HexToAddress("0x4CE687F9dDd42F26ad580f435acD0dE39e8f9c9C")
	expectedResult.signers = make(map[common.Address]*Signer)
	expectedResult.pendingBlockCh = make(chan *types.Block)
	expectedResult.quitSync = make(chan struct{})
	expectedResult.dialed = false

	tests := []struct {
		name string
		args args
		want *Handler
	}{
		{"testHandler1", args{testConfig, testEtherbase}, &expectedResult},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := NewHandler(tt.args.config, tt.args.etherbase)
			//pendingBlockCh and quitSync are expected to be different
			//thus, before reflect.DeepEqual(), we set both variables equalling to the expected value
			got.pendingBlockCh = expectedResult.pendingBlockCh
			got.quitSync = expectedResult.quitSync
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("NewHandler() = %v, \n want %v", got, tt.want)
			}
		})
	}
}
