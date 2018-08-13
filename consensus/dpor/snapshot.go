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

package dpor

import (
	"encoding/json"
	"log"
	"math/big"

	// "net/rpc"

	"github.com/ethereum/go-ethereum/accounts/abi/bind"
	"github.com/ethereum/go-ethereum/accounts/abi/bind/backends"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/dpor/election"
	"github.com/ethereum/go-ethereum/consensus/dpor/rpt"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/params"
	lru "github.com/hashicorp/golang-lru"
)

// Snapshot is the state of the authorization voting at a given point in time.
type Snapshot struct {
	config   *params.DporConfig // Consensus engine parameters to fine tune behavior
	sigcache *lru.ARCCache      // Cache of recent block signatures to speed up ecrecover

	Number uint64      `json:"number"` // Block number where the snapshot was created
	Hash   common.Hash `json:"hash"`   // Block hash where the snapshot was created

	Signers    map[uint64]common.Address   `json:"signers"`    // Set of authorized signers at this moment
	Recents    map[uint64]common.Address   `json:"recents"`    // Set of recent signers for spam protections
	Candidates map[common.Address]struct{} `json:"candidates"` // Set of candidates read from campaign contract

	// Signers    map[common.Address]struct{} `json:"signers"`    // Set of authorized signers at this moment
}

// newSnapshot creates a new snapshot with the specified startup parameters. This
// method does not initialize the set of recent signers, so only ever use if for
// the genesis block.
func newSnapshot(config *params.DporConfig, sigcache *lru.ARCCache, number uint64, hash common.Hash, signers []common.Address) *Snapshot {
	snap := &Snapshot{
		config:     config,
		sigcache:   sigcache,
		Number:     number,
		Hash:       hash,
		Signers:    make(map[uint64]common.Address),
		Recents:    make(map[uint64]common.Address),
		Candidates: make(map[common.Address]struct{}),
	}
	for idx, signer := range signers {
		snap.Signers[uint64(idx)] = signer
	}
	return snap
}

// loadSnapshot loads an existing snapshot from the database.
func loadSnapshot(config *params.DporConfig, sigcache *lru.ARCCache, db ethdb.Database, hash common.Hash) (*Snapshot, error) {
	blob, err := db.Get(append([]byte("dpor-"), hash[:]...))
	if err != nil {
		return nil, err
	}
	snap := new(Snapshot)
	if err := json.Unmarshal(blob, snap); err != nil {
		return nil, err
	}
	snap.config = config
	snap.sigcache = sigcache

	return snap, nil
}

// store inserts the snapshot into the database.
func (s *Snapshot) store(db ethdb.Database) error {
	blob, err := json.Marshal(s)
	if err != nil {
		return err
	}
	return db.Put(append([]byte("dpor-"), s.Hash[:]...), blob)
}

// copy creates a deep copy of the snapshot, though not the individual votes.
func (s *Snapshot) copy() *Snapshot {
	cpy := &Snapshot{
		config:     s.config,
		sigcache:   s.sigcache,
		Number:     s.Number,
		Hash:       s.Hash,
		Signers:    make(map[uint64]common.Address),
		Recents:    make(map[uint64]common.Address),
		Candidates: make(map[common.Address]struct{}),
	}
	for idx, signer := range s.Signers {
		cpy.Signers[idx] = signer
	}
	for block, signer := range s.Recents {
		cpy.Recents[block] = signer
	}
	for candidate := range s.Candidates {
		cpy.Candidates[candidate] = struct{}{}
	}
	return cpy
}

// apply creates a new authorization snapshot by applying the given headers to
// the original one.
func (s *Snapshot) apply(headers []*types.Header) (*Snapshot, error) {
	// Allow passing in no headers for cleaner code
	if len(headers) == 0 {
		return s, nil
	}
	// Sanity check that the headers can be applied
	for i := 0; i < len(headers)-1; i++ {
		if headers[i+1].Number.Uint64() != headers[i].Number.Uint64()+1 {
			return nil, errInvalidVotingChain
		}
	}
	if headers[0].Number.Uint64() != s.Number+1 {
		return nil, errInvalidVotingChain
	}
	// Iterate through the headers and create a new snapshot
	snap := s.copy()

	/*
		if uint64(len(headers)) != viewLength {
			return nil, errInvalidCheckpointApplyNumber
		}
		// TODO: implement viewChange( rpt calc call and elect calc call) here, then get net committee.
		snap = s.viewChange(headers, snap) // TODO: add block states to this func call.
	*/

	for _, header := range headers {
		err := snap.applyHeader(header)
		if err != nil {
			log.Fatal("Snapshot apply header error.")
		}
	}

	snap.Number += uint64(len(headers))
	snap.Hash = headers[len(headers)-1].Hash()

	return snap, nil
}

// TODO: finish this func to apply header to snapshot to calculate reputations of candidates fetched from candidate contract.
func (s *Snapshot) applyHeader(header *types.Header) error {
	// update snapshot attributes.
	s.Number = header.Number.Uint64()
	s.Hash = header.Hash()

	s.updateCandidates(header)
	s.updateRpts(header)

	if s.Number%checkpointInterval == 0 {
		s.updateView(header.Hash().Big().Int64())
	}
	return nil
}

// TODO: fix this logic.
func (s *Snapshot) updateCandidates(header *types.Header) error {
	var (
		key, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
		addr   = crypto.PubkeyToAddress(key.PublicKey)
	)
	// TODO: wrap this backend.
	contractBackend := backends.NewSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	transactOpts := bind.NewKeyedTransactor(key)
	instance, err := NewCampaign(transactOpts, common.HexToAddress(""), contractBackend)
	if err != nil {
		return err
	}

	candidates, err := instance.CandidatesOf(big.NewInt(int64(header.Number.Uint64() / viewLength)))
	if err != nil {
		return err
	}

	newCandidates := make(map[common.Address]struct{})
	for _, candidate := range candidates {
		newCandidates[candidate] = struct{}{}
	}
	s.Candidates = newCandidates

	return nil
}

// TODO: implement this func to get rpts for candidates. maybe save it as a map.
func (s *Snapshot) updateRpts(header *types.Header) error {
	return nil
}

// viewChange use rpt and election result to get new committee(signers).
func (s *Snapshot) updateView(seed int64) error {
	s.calcElection(seed)
	return nil
}

// TODO: finish this func.
func (s *Snapshot) calcElection(seed int64) (map[uint64]common.Address, error) {
	viewLength := int(s.config.Epoch)
	candidates := s.candidates()

	collector := rpt.BasicCollector{}
	rptDict := collector.GetRpts(&candidates)
	newSigners := election.Elect(rptDict, seed, viewLength)

	return newSigners, nil
}

// signers retrieves all signers in the committee.
func (s *Snapshot) signers() []common.Address {
	signers := make([]common.Address, 0, len(s.Signers))
	for _, signer := range s.Signers {
		signers = append(signers, signer)
	}
	return signers
}

func (s *Snapshot) isSigner(address common.Address) bool {
	result := false
	for idx, signer := range s.signers() {
		if address == signer {
			result = true
			break
		}
	}
	return result
}

// candidates retrieves all candidates recorded in the campaign contract.
func (s *Snapshot) candidates() []common.Address {
	candidates := make([]common.Address, 0, len(s.Candidates))
	for candidate := range s.Candidates {
		candidates = append(candidates, candidate)
	}
	return candidates
}

// inturn returns if a signer at a given block height is in-turn or not.
func (s *Snapshot) inturn(number uint64, signer common.Address) bool {
	signers, offset := s.signers(), 0
	for offset < len(signers) && signers[offset] != signer {
		offset++
	}
	return (number % uint64(len(signers))) == uint64(offset)
}
