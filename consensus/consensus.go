// Copyright 2017 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

// Package consensus implements different cpchain consensus engines.
package consensus

import (
	"math/big"

	"bitbucket.org/cpchain/chain/api/grpc"
	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/core/state"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

// ChainReader defines a small collection of methods needed to access the local
// blockchain.
type ChainReader interface {
	// Config retrieves the blockchain's chain configuration.
	Config() *configs.ChainConfig

	// CurrentHeader retrieves the current header from the local chain.
	CurrentHeader() *types.Header

	// GetHeader retrieves a block header from the database by hash and number.
	GetHeader(hash common.Hash, number uint64) *types.Header

	// GetHeaderByNumber retrieves a block header from the database by number.
	GetHeaderByNumber(number uint64) *types.Header

	// GetHeaderByHash retrieves a block header from the database by its hash.
	GetHeaderByHash(hash common.Hash) *types.Header

	// GetBlock retrieves a block from the database by hash and number.
	GetBlock(hash common.Hash, number uint64) *types.Block
}

// ChainWriter reads and writes pending block to blockchain
type ChainWriter interface {

	// InsertChain inserts blocks to chain, returns fail index and error
	InsertChain(chain types.Blocks) (int, error)
}

// ChainReadWriter includes reader and writer
type ChainReadWriter interface {
	ChainReader
	ChainWriter
}

// Engine is an algorithm agnostic consensus engine.
type Engine interface {
	// Author retrieves the cpchain address of the account that minted the given
	// block, which may be different from the header's coinbase if a consensus
	// engine is based on signatures.
	Author(header *types.Header) (common.Address, error)

	// VerifyHeader checks whether a header conforms to the consensus rules of a
	// given engine. Verifying the sigs may be done optionally here, or explicitly
	// via the VerifySeal method.
	// `refHeader' points to the original header, but `header' only points to a copy.
	VerifyHeader(chain ChainReader, header *types.Header, verifySigs bool, refHeader *types.Header) error

	// VerifyHeaders is similar to VerifyHeader, but verifies a batch of headers
	// concurrently. The method returns a quit channel to abort the operations and
	// a results channel to retrieve the async verifications (the order is that of
	// the input slice).
	VerifyHeaders(chain ChainReader, headers []*types.Header, verifySigs []bool, refHeaders []*types.Header) (chan<- struct{}, <-chan error)

	// VerifySigs checks whether the crypto seal on a header is valid according to
	// the consensus rules of the given engine.
	VerifySigs(chain ChainReader, header *types.Header, refHeader *types.Header) error

	// PrepareBlock initializes the consensus fields of a block header according to the
	// rules of a particular engine. The changes are executed inline.
	PrepareBlock(chain ChainReader, header *types.Header) error

	// Finalize runs any post-transaction state modifications (e.g. block rewards)
	// and assembles the final block.
	// Note: The block header and state database might be updated to reflect any
	// consensus rules that happen at finalization (e.g. block rewards).
	Finalize(chain ChainReader, header *types.Header, state *state.StateDB, txs []*types.Transaction,
		uncles []*types.Header, receipts []*types.Receipt) (*types.Block, error)

	// Seal generates a new block for the given input block with the local miner's
	// seal place on top.
	Seal(chain ChainReader, block *types.Block, stop <-chan struct{}) (*types.Block, error)

	// CalcDifficulty is the difficulty adjustment algorithm. It returns the difficulty
	// that a new block should have.
	CalcDifficulty(chain ChainReader, time uint64, parent *types.Header) *big.Int

	// APIs returns the RPC APIs this consensus engine provides.
	APIs(chain ChainReader) []rpc.API

	// GAPIs returns the GRPC APIs this consensus engine provides.
	GAPIs(chain ChainReader) []grpc.GApi
}

// Proposer is used to produce a block in our PV(Producer-Validator) model.
type Proposer interface {
	Engine
}

// Validator is used to validate and sign a block
type Validator interface {

	// ValidateBlock validates a basic field excepts seal of a block.
	ValidateBlock(chain ChainReader, block *types.Block) error

	// SignHeader signs a header in given state.
	SignHeader(chain ChainReader, header *types.Header, state State) error
}

// PbftEngine is a pbft based consensus engine
type PbftEngine interface {
	Engine

	// State returns current pbft phrase, one of (PrePrepare, Prepare, Commit).
	State() State

	// Start starts engine
	Start() error

	// Stop stops all
	Stop() error

	Protocol() Protocol
}

// State is the pbft state
type State uint8

const (
	// Idle state is served as the first state in PBFT, ready to receive the proposed block
	Idle State = iota

	// Preprepared state is the second state. The validator can enter this state after receiving proposed block (pre-prepare) message.
	// It is ready to send prepare messages
	Preprepared

	// Prepared state is the third state. The validator can enter it after collecting prepare certificate
	// It is about to broadcast commit messages
	Prepared

	// ImpeachPreprepared The validator transit to impeach pre-prepared state whenever the timer expires
	// It is about to broadcast impeach prepare messages
	ImpeachPreprepared

	// ImpeachPrepared Once a impeach prepare certificate is collected, a validator enters impeach prepared state
	ImpeachPrepared
)

// PbftStatus represents a state of a dpor replica
type PbftStatus struct {
	State State
	Head  *types.Header
}

// Protocol represents interfaces a protocol can provide
type Protocol interface {
	Version() uint

	Length() uint64

	Available() bool

	AddPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter) (string, bool, bool, error)

	RemovePeer(id string)

	HandleMsg(id string, msg p2p.Msg) error

	NodeInfo() interface{}
}
