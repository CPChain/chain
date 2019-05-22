package primitive_register

import (
	"context"
	"math/big"

	cpchain "bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/primitives"
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
	for addr, c := range MakePrimitiveContracts() {
		err := vm.RegisterPrimitiveContract(addr, c)
		if err != nil {
			log.Fatal("register primitive contract error", "error", err, "addr", addr)
		}
	}
}

func MakePrimitiveContracts() map[common.Address]vm.PrimitiveContract {
	contracts := make(map[common.Address]vm.PrimitiveContract)

	contracts[common.BytesToAddress([]byte{106})] = &primitives.CpuPowValidate{}
	contracts[common.BytesToAddress([]byte{107})] = &primitives.MemPowValidate{}
	return contracts
}
