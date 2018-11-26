package primitive_register

import (
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/primitives"
	"bitbucket.org/cpchain/chain/core/vm"
	"github.com/ethereum/go-ethereum/common"
)

type node interface {
	Service(service interface{}) error
	Attach() (*rpc.Client, error)
}

func RegisterPrimitiveContracts(n node) {
	rpcClient, err := n.Attach()
	if err != nil {
		log.Error("can't get rpc.client after start", "error", err)
	}
	client := cpclient.NewClient(rpcClient)
	for addr, c := range MakePrimitiveContracts(client) {
		vm.RegisterPrimitiveContract(addr, c)
	}

}

func MakePrimitiveContracts(client *cpclient.Client) map[common.Address]vm.PrimitiveContract {
	contracts := make(map[common.Address]vm.PrimitiveContract)

	// we start from 100 to reserve enough space for upstream primitive contracts.

	RptEvaluator, err := primitives.NewRptEvaluator(client)
	if err != nil {
		log.Fatal("s.RptEvaluator is file")
	}
	contracts[common.BytesToAddress([]byte{100})] = &primitives.GetRank{Backend: RptEvaluator}
	contracts[common.BytesToAddress([]byte{101})] = &primitives.GetMaintenance{Backend: RptEvaluator}
	contracts[common.BytesToAddress([]byte{102})] = &primitives.GetProxyCount{Backend: RptEvaluator}
	contracts[common.BytesToAddress([]byte{103})] = &primitives.GetUploadReward{Backend: RptEvaluator}
	contracts[common.BytesToAddress([]byte{104})] = &primitives.GetTxVolume{Backend: RptEvaluator}
	contracts[common.BytesToAddress([]byte{105})] = &primitives.IsProxy{Backend: RptEvaluator}
	contracts[common.BytesToAddress([]byte{106})] = &primitives.CpuPowValidate{}
	contracts[common.BytesToAddress([]byte{107})] = &primitives.MemPowValidate{}
	return contracts
}
