package primitive_register

import (
	"context"
	"math/big"

	"bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/primitives"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/rpt_backend_holder"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// this ContractAPI only use read contract can't Write or Event filtering
type ContractAPI interface {
	CodeAt(ctx context.Context, contract common.Address, blockNumber *big.Int) ([]byte, error)
	CallContract(ctx context.Context, call cpchain.CallMsg, blockNumber *big.Int) ([]byte, error)
	PendingCodeAt(ctx context.Context, contract common.Address) ([]byte, error)
	PendingCallContract(ctx context.Context, call cpchain.CallMsg) ([]byte, error)
	PendingNonceAt(ctx context.Context, account common.Address) (uint64, error)
	SuggestGasPrice(ctx context.Context) (*big.Int, error)
	EstimateGas(ctx context.Context, call cpchain.CallMsg) (gas uint64, err error)
	SendTransaction(ctx context.Context, tx *types.Transaction) error
	FilterLogs(ctx context.Context, query cpchain.FilterQuery) ([]types.Log, error)
	SubscribeFilterLogs(ctx context.Context, query cpchain.FilterQuery, ch chan<- types.Log) (cpchain.Subscription, error)
}

func RegisterPrimitiveContracts() {
	chainClient := getChainClient()
	// d.SetRptBackend(chainClient)
	for addr, c := range MakePrimitiveContracts(chainClient, chainClient) {
		err := vm.RegisterPrimitiveContract(addr, c)
		if err != nil {
			log.Fatal("register primitive contract error", "error", err, "addr", addr)
		}
	}
}

func getChainClient() *rpt_backend_holder.RptApiClient {
	return &rpt_backend_holder.RptApiClient{ChainBackend: rpt_backend_holder.GetApiBackendHolderInstance().ChainBackend, ContractBackend: rpt_backend_holder.GetApiBackendHolderInstance().ContractBackend}
}

func MakePrimitiveContracts(contractClient bind.ContractBackend, chainClient *rpt_backend_holder.RptApiClient) map[common.Address]vm.PrimitiveContract {
	contracts := make(map[common.Address]vm.PrimitiveContract)

	// we start from 100 to reserve enough space for upstream primitive contracts.
	RptEvaluator, err := primitives.NewRptEvaluator(contractClient, chainClient)
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
