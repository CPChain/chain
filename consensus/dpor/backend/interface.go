package backend

import (
	"context"
	"math/big"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
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

// VerifySignerFn verifies if a signer is a signer at given term
type VerifySignerFn func(address common.Address, term uint64) (bool, error)

// VerifyFutureSigner verifies if a signer is proposer or validator from term to future term
func VerifyFutureSigner(address common.Address, term uint64, futureTerm uint64, verifyProposerFn VerifySignerFn, verifyValidatorFn VerifySignerFn) (bool, bool, error) {

	isProposer, isValidator := false, false
	for t := term; t <= futureTerm; t++ {
		isP, _ := verifyProposerFn(address, t)
		isV, _ := verifyValidatorFn(address, t)
		isProposer = isProposer || isP
		isValidator = isValidator || isV
	}

	return isProposer, isValidator, nil
}

// DporService provides functions used by dpor handler
type DporService interface {
	// TermOf returns the term number of given block number
	TermOf(number uint64) uint64

	// FutureTermOf returns the future term number of given block number
	FutureTermOf(number uint64) uint64

	// VerifyProposerOf verifies if an address is a proposer of given term
	VerifyProposerOf(signer common.Address, term uint64) (bool, error)

	// VerifyValidatorOf verifies if an address is a validator of given term
	VerifyValidatorOf(signer common.Address, term uint64) (bool, error)

	// ValidatorsOf returns the list of validators in committee for the specified block number
	ValidatorsOf(number uint64) ([]common.Address, error)

	// ProposersOf returns the list of proposers in committee for the specified block number
	ProposersOf(number uint64) ([]common.Address, error)

	// ValidatorsOfTerm returns the list of validators in committee for the specified term
	ValidatorsOfTerm(term uint64) ([]common.Address, error)

	// ProposersOfTerm returns the list of proposers in committee for the specified term
	ProposersOfTerm(term uint64) ([]common.Address, error)

	// VerifyHeaderWithState verifies the given header
	// if in preprepared state, verify basic fields
	// if in prepared state, verify if enough prepare sigs
	// if in committed state, verify if enough commit sigs
	VerifyHeaderWithState(header *types.Header, state consensus.State) error

	// ValidateBlock verifies a block
	ValidateBlock(block *types.Block) error

	// SignHeader signs the block if not signed it yet
	SignHeader(header *types.Header, state consensus.State) error

	// BroadcastBlock broadcasts a block to normal peers(not pbft replicas)
	BroadcastBlock(block *types.Block, prop bool)

	// InsertChain inserts a block to chain
	InsertChain(block *types.Block) error

	// Status returns a pbft replica's status
	Status() *consensus.PbftStatus

	// StatusUpdate updates status of dpor
	StatusUpdate() error

	// CreateImpeachBlock returns an impeachment block for view change
	CreateImpeachBlock() (*types.Block, error)

	// GetCurrentBlock returns current block
	GetCurrentBlock() *types.Block

	// HasBlockInChain returns if a block is in local chain
	HasBlockInChain(hash common.Hash, number uint64) bool

	// ImpeachTimeout returns the timeout for impeachment
	ImpeachTimeout() time.Duration

	// EcrecoverSigs recovers signer address and corresponding signature, it ignores empty signature and return empty
	// addresses if one of the sigs are illegal
	EcrecoverSigs(header *types.Header, state consensus.State) ([]common.Address, []types.DporSignature, error)

	// Update the signature to prepare signature cache(two kinds of sigs, one for prepared, another for final)
	UpdatePrepareSigsCache(validator common.Address, hash common.Hash, sig types.DporSignature)

	// Update the signature to final signature cache(two kinds of sigs, one for prepared, another for final)
	UpdateFinalSigsCache(validator common.Address, hash common.Hash, sig types.DporSignature)
}

type HandlerMode uint

const (
	PBFTMode HandlerMode = iota
	LBFTMode
)
