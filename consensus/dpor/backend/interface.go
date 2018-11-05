package backend

import (
	"context"
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

// ClientBackend is the client operation interface
type ClientBackend interface {
	ChainBackend
	ContractBackend
}

// ChainBackend is the chain client operation interface
type ChainBackend interface {
	BalanceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (*big.Int, error)
	BlockByNumber(ctx context.Context, number *big.Int) (*types.Block, error)
	HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error)
}

// ContractBackend  is the contract client operation interface
type ContractBackend interface {
	bind.ContractBackend
	TransactionReceipt(ctx context.Context, txHash common.Hash) (*types.Receipt, error)
}

// ContractCaller is used to call the contract with given key and client.
type ContractCaller struct {
	Key    *keystore.Key
	Client ClientBackend

	GasLimit uint64
}

// NewContractCaller returns a ContractCaller.
func NewContractCaller(key *keystore.Key, client ClientBackend, gasLimit uint64) (*ContractCaller, error) {
	return &ContractCaller{
		Key:      key,
		Client:   client,
		GasLimit: gasLimit,
	}, nil
}

// RsaReader reads a rsa key
type RsaReader func() (*rsakey.RsaKey, error)

// PbftHandler is a handler represents all possible methods a node can provide to do consensus protocol requests.
type PbftHandler interface {
	SetServer(srv *p2p.Server) error

	SetRsaKey(rsaReader RsaReader) error

	SetContractCaller(cc *ContractCaller) error

	UpdateSigners(epochIdx uint64, signers []common.Address) error

	Start() error

	Stop() error

	SendMsg(addr common.Address, msg interface{}) error

	BroadcastMsg(msg interface{}) error
}
