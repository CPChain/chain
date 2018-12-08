package apibackend_holder

import (
	"sync"

	"context"
	"math/big"

	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/core/state"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
)

// used to hold *APIBackend
type APIBackendHolder struct {
	ApiBackend ChainAPIBackend
}

var apiBackendHolderInstance *APIBackendHolder
var onceApiBackendHoldCreation sync.Once
var onceApiBackendHoldInit sync.Once

func GetApiBackendHolderInstance() *APIBackendHolder {
	onceApiBackendHoldCreation.Do(func() {
		apiBackendHolderInstance = &APIBackendHolder{}
	})
	return apiBackendHolderInstance
}

func (p *APIBackendHolder) Init(apiBackend ChainAPIBackend) {
	onceApiBackendHoldInit.Do(func() {
		log.Info("init APIBackendHolder", "apiBackend", apiBackend)
		p.ApiBackend = apiBackend
	})
}

type ChainClient struct {
	ChainAPIBackend
}

type ChainAPIBackend interface {
	StateAndHeaderByNumber(ctx context.Context, blockNr rpc.BlockNumber, isPrivate bool) (*state.StateDB, *types.Header, error)
	BlockByNumber(ctx context.Context, number rpc.BlockNumber) (*types.Block, error)
	HeaderByNumber(ctx context.Context, number rpc.BlockNumber) (*types.Header, error)
}

type ChainApiClient struct {
	ApiBackend ChainAPIBackend
}

// BalanceAt returns the wei balance of the given account.
// The block number can be nil, in which case the balance is taken from the latest known block.
func (cc *ChainApiClient) BalanceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (*hexutil.Big, error) {
	log.Debug("BalanceAt", "addr", account.Hex(), "number", blockNumber)
	state, _, err := cc.ApiBackend.StateAndHeaderByNumber(ctx, rpc.BlockNumber(blockNumber.Uint64()), false)
	if state == nil || err != nil {
		return nil, err
	}
	return (*hexutil.Big)(state.GetBalance(account)), state.Error()
}

// BlockByNumber returns a block from the current canonical chain. If number is nil, the
// latest known block is returned.
func (cc *ChainApiClient) BlockByNumber(ctx context.Context, number *big.Int) (*types.Block, error) {
	log.Debug(" BlockByNumber", "number", number)
	return cc.ApiBackend.BlockByNumber(ctx, rpc.BlockNumber(number.Uint64()))
}

// HeaderByNumber returns a block header from the current canonical chain. If number is
// nil, the latest known header is returned.
func (cc *ChainApiClient) HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error) {
	log.Debug("HeaderByNumber", "number", number)
	return cc.ApiBackend.HeaderByNumber(ctx, rpc.BlockNumber(number.Uint64()))
}
