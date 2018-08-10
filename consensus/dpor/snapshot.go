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
	// "log"
	"strconv"

	// "net/rpc"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/dpor/election"
	"github.com/ethereum/go-ethereum/consensus/dpor/rpt"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/log"
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
	for _, header := range headers {
		log.Info(strconv.Itoa(int(header.Number.Uint64())))
	}

	if headers[0].Number.Uint64() != s.Number+1 {
		return nil, errInvalidVotingChain
	}
	// Iterate through the headers and create a new snapshot
	snap := s.copy()

	for _, header := range headers {
		err := snap.applyHeader(header)
		if err != nil {
			log.Warn("Snapshot apply header error.", err)
			return nil, err
		}
	}

	snap.Number = headers[len(headers)-1].Number.Uint64()
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
	// TODO: delete this.
	candidates := []common.Address{
		common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"),
		common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092"),
		common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465"),
	}
	// TODO: above is wrong.
	// TODO: delete this.

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

	// TODO: fix this.
	rptDict[0] = rpt.RPT{
		Address: common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"),
		Rpt:     50,
	}
	rptDict[1] = rpt.RPT{
		Address: common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092"),
		Rpt:     100,
	}
	rptDict[2] = rpt.RPT{
		Address: common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465"),
		Rpt:     20,
	}

	// TODO: delete this.
	log.Info("election params:")
	log.Info("seed: " + strconv.Itoa(int(seed)))
	log.Info("viewLength: " + strconv.Itoa(int(viewLength)))
	log.Info("candidates:")
	for _, rpt := range rptDict {
		log.Info(rpt.Address.Hex() + ": " + strconv.Itoa(int(rpt.Rpt)))
	}
	// TODO: delete this.

	newSigners := election.Elect(rptDict, seed, viewLength)

	s.Signers = newSigners

	return newSigners, nil
}

// signers retrieves all signers in the committee.
func (s *Snapshot) signers() []common.Address {
	signers := make([]common.Address, 0, len(s.Signers))
	for i := 0; i < len(s.Signers); i++ {
		signers = append(signers, s.Signers[uint64(i)])
	}
	return signers
}

func (s *Snapshot) isSigner(address common.Address) bool {
	result := false
	for _, signer := range s.signers() {
		if address == signer {
			result = true
			break
		}
	}
	return result
}

func (s *Snapshot) isLeader(number uint64, signer common.Address) bool {

	// TODO: delete this.
	log.Info("checking leader: number:" + strconv.Itoa(int(number)) + "signer:" + signer.Hex())
	log.Info("leader:" + s.signers()[(number-1)%viewLength].Hex())
	// TODO: delete this.

	result := false
	if signer == s.signers()[(number-1)%viewLength] {
		result = true
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
