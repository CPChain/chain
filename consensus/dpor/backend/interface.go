package backend

import (
	"context"
	"errors"
	"math/big"
	"strconv"
	"strings"
	"time"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/commons/log"
	times "bitbucket.org/cpchain/chain/commons/time"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/p2p"
)

var (
	// defaultTimeGapAllowed is the time gap allowed to build connection with remote peer
	defaultTimeGapAllowed = time.Second * time.Duration(times.MaxGapDuration)
)

// Action is type enumerator for FSM action
type Action uint8

// Those actions are the result after handleMsg returned
const (
	NoAction Action = iota
	BroadcastMsgAction
	BroadcastAndInsertBlockAction
)

// MsgCode is type enumerator for FSM message type
type MsgCode uint8

// Those are msg codes used in fsm
const (
	NoMsgCode MsgCode = iota

	PreprepareMsgCode
	PrepareMsgCode
	CommitMsgCode
	PrepareAndCommitMsgCode
	ValidateMsgCode

	ImpeachPreprepareMsgCode
	ImpeachPrepareMsgCode
	ImpeachCommitMsgCode
	ImpeachPrepareAndCommitMsgCode
	ImpeachValidateMsgCode
)

var (
	msgCodeName = map[MsgCode]string{
		NoMsgCode:                      "NoMsgCode",
		PreprepareMsgCode:              "PreprepareMsgCode",
		PrepareMsgCode:                 "PrepareMsgCode",
		CommitMsgCode:                  "CommitMsgCode",
		PrepareAndCommitMsgCode:        "PrepareAndCommitMsgCode",
		ValidateMsgCode:                "ValidateMsgCode",
		ImpeachPreprepareMsgCode:       "ImpeachPreprepareMsgCode",
		ImpeachPrepareMsgCode:          "ImpeachPrepareMsgCode",
		ImpeachCommitMsgCode:           "ImpeachCommitMsgCode",
		ImpeachPrepareAndCommitMsgCode: "ImpeachPrepareAndCommitMsgCode",
		ImpeachValidateMsgCode:         "ImpeachValidateMsgCode",
	}
)

func (mc MsgCode) String() string {
	if name, ok := msgCodeName[mc]; ok {
		return name
	}
	return "Unknown MsgCode"
}

// DSMStatus represents a Dpor State Machine Status
type DSMStatus struct {
	Number uint64
	// TODO: i need hash here
	State consensus.State
}

// ClientBackend is the client operation interface
type ClientBackend interface {
	ChainBackend
	ContractBackend
}

// ChainBackend is the chain client operation interface
type ChainBackend interface {
	HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error)
	BalanceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (*big.Int, error)
	NonceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (uint64, error)
}

// ImpeachedProposer returns the impeached proposer of a header if the block is an impeach block
func ImpeachedProposer(header *types.Header) (common.Address, error) {

	if header == nil || header.Number == nil {
		return common.Address{}, errors.New("invalid header to retrieve the impeached proposer")
	}

	if !header.Impeachment() {
		return common.Address{}, errors.New("cannot retrieve impeached proposer from an non-impeach block header")
	}

	blockNumber := header.Number.Uint64()
	viewLen, termLen := configs.ChainConfigInfo().Dpor.ViewLen, configs.ChainConfigInfo().Dpor.TermLen
	proposerIndex := ((blockNumber - 1) % (viewLen * termLen)) % termLen

	if len(header.Dpor.Proposers) != int(termLen) {
		return common.Address{}, errors.New("invalid header.Dpor.Proposers list, length is not" + strconv.Itoa(int(termLen)))
	}

	return header.Dpor.Proposers[proposerIndex], nil
}

// ContractBackend is the contract client operation interface
type ContractBackend interface {
	bind.ContractBackend
}

// ContractCaller is used to call the contract with given key and client.
// TODO: remove this later
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

// VerifyBlockFn verifies basic fields of a block
type VerifyBlockFn func(block *types.Block) error

// SignFn is a signer callback function to request a hash to be signed by a
// backing account.
type SignFn func(accounts.Account, []byte) ([]byte, error)

// HandleGeneratedImpeachBlock handles generated impeach block
type HandleGeneratedImpeachBlock func(block *types.Block) error

// ConsensusStateMachine is a state machine used for consensus protocol for validators msg processing
type ConsensusStateMachine interface {
	Status() DSMStatus
	Faulty() uint64
	FSM(input *BlockOrHeader, msgCode MsgCode) ([]*BlockOrHeader, Action, MsgCode, error)
}

// DporService provides functions used by dpor handler
type DporService interface {

	// Coinbase returns current coinbase
	Coinbase() common.Address

	// TermLength returns term length
	TermLength() uint64

	// Faulty returns the number of faulty nodes
	Faulty() uint64

	// ViewLength returns view length
	ViewLength() uint64

	// ValidatorsNum returns number of validators
	ValidatorsNum() uint64

	// Period returns period of block generation
	Period() time.Duration

	// BlockDelay returns max delay of preprepare block propagation
	BlockDelay() time.Duration

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

	// ProposerOf returns the proposer of the specified block number by rpt and election calculation
	ProposerOf(number uint64) (common.Address, error)

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
	ValidateBlock(block *types.Block, verifySigs bool, verifyProposers bool) error

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

	// CreateImpeachBlock returns an impeachment block
	CreateImpeachBlock() (*types.Block, error)

	// CreateFailbackImpeachBlocks creates impeachment blocks with failback timestamps
	CreateFailbackImpeachBlocks() (firstImpeachment *types.Block, secondImpeachment *types.Block, err error)

	// GetCurrentBlock returns current block
	GetCurrentBlock() *types.Block

	// HasBlockInChain returns if a block is in local chain
	HasBlockInChain(hash common.Hash, number uint64) bool

	// GetBlockFromChain returns a block from local chain with given hash and number
	GetBlockFromChain(hash common.Hash, number uint64) *types.Block

	// ImpeachTimeout returns the timeout for impeachment
	ImpeachTimeout() time.Duration

	// ECRecoverProposer recovers proposer's address from a seal of a header
	ECRecoverProposer(header *types.Header) (common.Address, error)

	// ECRecoverSigs recovers signer address and corresponding signature, it ignores empty signature and return empty
	// addresses if one of the sigs are illegal
	ECRecoverSigs(header *types.Header, state consensus.State) ([]common.Address, []types.DporSignature, error)

	// Update the signature to prepare signature cache(two kinds of sigs, one for prepared, another for final)
	UpdatePrepareSigsCache(validator common.Address, hash common.Hash, sig types.DporSignature)

	// Update the signature to final signature cache(two kinds of sigs, one for prepared, another for final)
	UpdateFinalSigsCache(validator common.Address, hash common.Hash, sig types.DporSignature)

	// GetMac signs a Mac
	GetMac() (string, []byte, error)

	// SyncFrom tries to sync block from given peer
	SyncFrom(p *p2p.Peer)

	// Synchronize tries to sync block from best peer
	Synchronize()
}

// HandlerMode indicates the run mode of handler
type HandlerMode int

// Those are handler mode
const (
	LBFTMode HandlerMode = iota
	LBFT2Mode
)

// ValidMacSig recovers an address from a signed mac
func ValidMacSig(mac string, sig []byte) (valid bool, signer common.Address, err error) {

	log.Debug("received mac", "mac", mac)

	// check if mac prefix is valid
	split := "|"
	s := strings.Split(mac, split)
	if len(s) != 2 {
		log.Warn("wrong mac format", "mac", mac)
		return
	}
	prefix, timeString := s[0], s[1]
	if prefix != "cpchain" {
		log.Warn("wrong mac prefix", "prefix", prefix)
		return
	}

	// check if remote time is valid
	remoteTime, err := time.Parse(time.RFC3339, timeString)
	if err != nil {
		log.Warn("err when parsing time string", "time", timeString)
		return
	}
	timeGap := time.Now().Sub(remoteTime)
	log.Debug("remote time", "time", remoteTime.Format(time.RFC3339))
	log.Debug("local time", "time", time.Now().Format(time.RFC3339))
	log.Debug("time gap", "seconds", timeGap.Seconds())

	if timeGap > defaultTimeGapAllowed {
		return
	}

	var hash common.Hash
	hasher := sha3.NewKeccak256()
	hasher.Write([]byte(mac))
	hasher.Sum(hash[:0])

	// recover address
	pubkey, err := crypto.Ecrecover(hash.Bytes(), sig)
	if err != nil {
		return
	}
	copy(signer[:], crypto.Keccak256(pubkey[1:])[12:])

	// check passed
	valid = true

	return
}

// IsCheckPoint returns if a given block number is in a checkpoint with given
// termLen and viewLen
func IsCheckPoint(number uint64, termLen uint64, viewLen uint64) bool {
	if number == 0 {
		return false
	}

	if termLen == 0 || viewLen == 0 {
		return true
	}
	return number%(termLen*viewLen) == 0
}

// TermOf returns the term index of given block number
func TermOf(blockNum uint64) uint64 {
	if blockNum == 0 {
		return 0 // block number 0 is a special case, its term is set to 0
	}

	termLen := configs.ChainConfigInfo().Dpor.TermLen
	viewLen := configs.ChainConfigInfo().Dpor.ViewLen

	return (blockNum - 1) / (termLen * viewLen)
}
