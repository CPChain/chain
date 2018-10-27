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

// Package dpor implements the dpor consensus engine.
package dpor

import (
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/ethdb"
	"github.com/ethereum/go-ethereum/common"
	lru "github.com/hashicorp/golang-lru"
)

const (
	inmemorySnapshots  = 1000 // Number of recent vote snapshots to keep in memory
	inmemorySignatures = 1000 // Number of recent block signatures to keep in memory

	pctA = 2
	pctB = 3 // only when n > 2/3 * N, accept the block
)

// Dpor is the proof-of-reputation consensus engine proposed to support the
// cpchain testnet.
type Dpor struct {
	dh     dporHelper
	db     ethdb.Database      // Database to store and retrieve Snapshot checkpoints
	config *configs.DporConfig // Consensus engine configuration parameters

	recents    *lru.ARCCache // Snapshots for recent block to speed up reorgs
	signatures *lru.ARCCache // Signatures of recent blocks to speed up mining

	signedBlocks map[uint64]common.Hash // record signed blocks.

	signer common.Address // Ethereum address of the signing key
	signFn SignerFn       // Signer function to authorize hashes with

	committeeNetworkHandler consensus.CommitteeNetworkHandler

	fake           bool // used for test, always accept a block.
	fakeFail       uint64
	fakeDelay      time.Duration // Time delay to sleep for before returning from verify
	contractCaller *consensus.ContractCaller

	lock sync.RWMutex // Protects the signer fields
}

// New creates a Dpor proof-of-reputation consensus engine with the initial
// signers set to the ones provided by the user.
func New(config *configs.DporConfig, db ethdb.Database) *Dpor {

	// Set any missing consensus parameters to their defaults
	conf := *config
	if conf.Epoch == 0 {
		conf.Epoch = uint64(epochLength)
	}
	if conf.View == 0 {
		conf.View = uint64(viewLength)
	}

	// Allocate the Snapshot caches and create the engine
	recents, _ := lru.NewARC(inmemorySnapshots)
	signatures, _ := lru.NewARC(inmemorySignatures)

	signedBlocks := make(map[uint64]common.Hash)

	return &Dpor{
		dh:           &defaultDporHelper{&defaultDporUtil{}},
		config:       &conf,
		db:           db,
		recents:      recents,
		signatures:   signatures,
		signedBlocks: signedBlocks,
	}
}

func NewFaker(config *configs.DporConfig, db ethdb.Database) *Dpor {
	d := New(config, db)
	d.fake = true
	return d
}

func NewFakeFailer(config *configs.DporConfig, db ethdb.Database, fail uint64) *Dpor {
	d := NewFaker(config, db)
	d.fakeFail = fail
	return d
}

func NewFakeDelayer(config *configs.DporConfig, db ethdb.Database, delay time.Duration) *Dpor {
	d := NewFaker(config, db)
	d.fakeDelay = delay
	return d
}

// SetContractCaller sets dpor.contractCaller
func (d *Dpor) SetContractCaller(contractCaller *consensus.ContractCaller) error {
	d.lock.Lock()
	defer d.lock.Unlock()
	d.contractCaller = contractCaller
	return nil
}

// SetCommitteeNetworkHandler sets dpor.committeeNetworkHandler
func (d *Dpor) SetCommitteeNetworkHandler(committeeNetworkHandler consensus.CommitteeNetworkHandler) error {
	d.lock.Lock()
	defer d.lock.Unlock()
	d.committeeNetworkHandler = committeeNetworkHandler
	return nil
}
