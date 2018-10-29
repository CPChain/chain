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
	"errors"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor/election"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"
	"bitbucket.org/cpchain/chain/ethdb"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

const (

	// EpochGapBetweenElectionAndMining is the the epoch gap between election and mining.
	EpochGapBetweenElectionAndMining = 3

	// MaxSizeOfRecentSigners is the size of the RecentSigners.
	MaxSizeOfRecentSigners = 10
)

var (
	errSignerNotInCommittee = errors.New("signer not in committee")
	errGenesisBlockNumber   = errors.New("genesis block has no leader")
)

// Snapshot is used to check if a received block is valid by create a snapshot from previous blocks
type Snapshot interface {
	store(db ethdb.Database) error
	copy() *Snapshot
	apply(headers []*types.Header) (*Snapshot, error)
	applyHeader(header *types.Header) error
	updateCandidates(header *types.Header) error
	updateRpts(header *types.Header) (rpt.RPTs, error)
	updateView(rpts rpt.RPTs, seed int64, viewLength int) error
	signers() []common.Address
	signerRound(signer common.Address) (int, error)
	isSigner(signer common.Address) bool
	isLeader(signer common.Address, number uint64) (bool, error)
	candidates() []common.Address
	inturn(number uint64, signer common.Address) bool
}

// DporSnapshot is the state of the authorization voting at a given point in time.
type DporSnapshot struct {
	Number        uint64                      `json:"number"`     // Block number where the Snapshot was created
	Hash          common.Hash                 `json:"hash"`       // Block hash where the Snapshot was created
	Candidates    []common.Address            `json:"candidates"` // Set of candidates read from campaign contract
	RecentSigners map[uint64][]common.Address `json:"signers"`    // Set of recent signers
	// RecentSigners *lru.ARCCache    `json:"signers"`

	config         *configs.DporConfig // Consensus engine parameters to fine tune behavior
	ContractCaller *consensus.ContractCaller

	lock sync.RWMutex
}

func (s *DporSnapshot) number() uint64 {
	s.lock.Lock()
	defer s.lock.Unlock()

	return s.Number
}

func (s *DporSnapshot) setNumber(number uint64) {
	s.lock.Lock()
	defer s.lock.Unlock()

	s.Number = number
}

func (s *DporSnapshot) setHash(hash common.Hash) {
	s.lock.Lock()
	defer s.lock.Unlock()

	s.Hash = hash
}

func (s *DporSnapshot) hash() common.Hash {
	s.lock.Lock()
	defer s.lock.Unlock()

	return s.Hash
}

func (s *DporSnapshot) candidates() []common.Address {
	s.lock.Lock()
	defer s.lock.Unlock()

	return s.Candidates
}

func (s *DporSnapshot) setCandidates(candidates []common.Address) {
	s.lock.Lock()
	defer s.lock.Unlock()

	s.Candidates = candidates
}

func (s *DporSnapshot) recentSigners() map[uint64][]common.Address {
	s.lock.Lock()
	defer s.lock.Unlock()

	return s.RecentSigners
}

func (s *DporSnapshot) getRecentSigners(epochIdx uint64) []common.Address {
	s.lock.Lock()
	defer s.lock.Unlock()

	signers, ok := s.RecentSigners[epochIdx]
	if !ok {
		return nil
	}

	return signers
}

func (s *DporSnapshot) setRecentSigners(epochIdx uint64, signers []common.Address) {
	s.lock.Lock()
	defer s.lock.Unlock()

	s.RecentSigners[epochIdx] = signers

	previousEpochIdx := epochIdx - EpochGapBetweenElectionAndMining - MaxSizeOfRecentSigners
	if _, ok := s.RecentSigners[previousEpochIdx]; ok {
		delete(s.RecentSigners, previousEpochIdx)
	}
}

func (s *DporSnapshot) contractCaller() *consensus.ContractCaller {
	s.lock.Lock()
	defer s.lock.Unlock()

	return s.ContractCaller
}

func (s *DporSnapshot) setContractCaller(contractCaller *consensus.ContractCaller) {
	s.lock.Lock()
	defer s.lock.Unlock()

	s.ContractCaller = contractCaller
}

// newSnapshot creates a new Snapshot with the specified startup parameters. This
// method does not initialize the set of recent signers, so only ever use if for
// the genesis block.
func newSnapshot(config *configs.DporConfig, number uint64, hash common.Hash, signers []common.Address) *DporSnapshot {
	snap := &DporSnapshot{
		config:        config,
		Number:        number,
		Hash:          hash,
		RecentSigners: make(map[uint64][]common.Address),
	}

	snap.setRecentSigners(snap.EpochIdx(), signers)
	return snap
}

// loadSnapshot loads an existing Snapshot from the database.
func loadSnapshot(config *configs.DporConfig, db ethdb.Database, hash common.Hash) (*DporSnapshot, error) {

	// Retrieve from db
	blob, err := db.Get(append([]byte("dpor-"), hash[:]...))
	if err != nil {
		return nil, err
	}

	// Recover it!
	snap := new(DporSnapshot)
	if err := json.Unmarshal(blob, snap); err != nil {
		return nil, err
	}
	snap.config = config

	return snap, nil
}

// store inserts the Snapshot into the database.
func (s *DporSnapshot) store(db ethdb.Database) error {
	blob, err := json.Marshal(s)
	if err != nil {
		return err
	}
	return db.Put(append([]byte("dpor-"), s.Hash[:]...), blob)
}

// copy creates a deep copy of the Snapshot, though not the individual votes.
func (s *DporSnapshot) copy() *DporSnapshot {
	cpy := &DporSnapshot{
		config:     s.config,
		Number:     s.number(),
		Hash:       s.hash(),
		Candidates: make([]common.Address, len(s.Candidates)),
	}

	cpy.RecentSigners = s.RecentSigners
	copy(cpy.Candidates, s.candidates())

	return cpy
}

// apply creates a new authorization Snapshot by applying the given headers to
// the original one.
func (s *DporSnapshot) apply(headers []*types.Header, contractCaller *consensus.ContractCaller) (*DporSnapshot, error) {
	// Allow passing in no headers for cleaner code
	if len(headers) == 0 {
		return s, nil
	}

	// Sanity check that the headers can be applied
	for i := 0; i < len(headers)-1; i++ {
		if headers[i+1].Number.Uint64() != headers[i].Number.Uint64()+1 {
			return nil, errInvalidChain
		}
	}
	if headers[0].Number.Uint64() != s.Number+1 {
		return nil, errInvalidChain
	}

	// Iterate through the headers and create a new Snapshot
	snap := s.copy()
	snap.setContractCaller(contractCaller)
	for _, header := range headers {
		err := snap.applyHeader(header)
		if err != nil {
			log.Warn("DporSnapshot apply header error.", err)
			return nil, err
		}
	}

	snap.setNumber(headers[len(headers)-1].Number.Uint64())
	snap.setHash(headers[len(headers)-1].Hash())

	return snap, nil
}

// applyHeader applys header to Snapshot to calculate reputations of candidates fetched from candidate contract
func (s *DporSnapshot) applyHeader(header *types.Header) error {

	// Update Snapshot attributes.
	s.setNumber(header.Number.Uint64())
	s.setHash(header.Hash())

	// Update candidates
	err := s.updateCandidates(header)
	if err != nil {
		log.Warn("err when update candidates", "err", err)
		return err
	}

	// Update rpts
	rpts, err := s.updateRpts(header)
	if err != nil {
		log.Warn("err when update rpts", "err", err)
		return err
	}

	// If in checkpoint, run election
	if IsCheckPoint(s.number(), s.config.Epoch, s.config.View) {
		seed := header.Hash().Big().Int64()
		err := s.updateSigners(rpts, seed)
		if err != nil {
			log.Warn("err when run election", "err", err)
			return err
		}
	}

	return nil
}

// updateCandidates updates candidates from campaign contract
func (s *DporSnapshot) updateCandidates(header *types.Header) error {

	// Default Signers/Candidates
	candidates := []common.Address{
		common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"),
		common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092"),
		common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465"),
		common.HexToAddress("0x3a18598184ef84198db90c28fdfdfdf56544f747"),
	}

	contractCaller := s.contractCaller()

	// If contractCaller is not nil, use it to update candidates from contract
	if contractCaller != nil {

		// Creates an contract instance
		campaignAddress := s.config.Contracts["campaign"]
		contractInstance, err := contract.NewCampaign(campaignAddress, contractCaller.Client)
		if err != nil {
			return err
		}

		// Read candidates from the contract instance
		cds, err := contractInstance.CandidatesOf(nil, big.NewInt(1))
		if err != nil {
			return err
		}

		// If useful, use it!
		if uint64(len(cds)) > s.config.Epoch {
			candidates = cds
		}
	}

	s.setCandidates(candidates)
	return nil
}

// updateRpts updates rpts of candidates
func (s *DporSnapshot) updateRpts(header *types.Header) (rpt.RPTs, error) {

	// TODO: use rpt collector to update rpts.
	var rpts rpt.RPTs
	for idx, candidate := range s.candidates() {
		r := rpt.RPT{Address: candidate, Rpt: float64(idx)}
		rpts = append(rpts, r)
	}

	return rpts, nil
}

func (s *DporSnapshot) ifUseDefaultSigners() bool {
	return s.number() < s.config.MaxInitBlockNumber
}

func (s *DporSnapshot) ifStartElection() bool {
	return s.number() >= s.config.MaxInitBlockNumber-(s.config.Epoch*(EpochGapBetweenElectionAndMining-1)*s.config.View)
}

// updateView use rpt and election result to get new committee(signers)
func (s *DporSnapshot) updateSigners(rpts rpt.RPTs, seed int64) error {

	signers := s.candidates()[:s.config.Epoch]

	// Use default signers
	if s.ifUseDefaultSigners() {
		s.setRecentSigners(s.EpochIdx()+1, signers)
	}

	// Elect signers
	if s.ifStartElection() {
		epochIdx := s.FutureEpochIdxOf(s.number())
		signers := s.getRecentSigners(epochIdx)

		if len(signers) == 0 {
			signers = election.Elect(rpts, seed, int(s.config.Epoch))
			s.setRecentSigners(epochIdx, signers)
		}
	}

	return nil
}

// EpochIdx returns the epoch index of current block number
func (s *DporSnapshot) EpochIdx() uint64 {
	if s.number() == 0 {
		return 0
	}
	return (s.number() - 1) / ((s.config.Epoch) * (s.config.View))
}

// EpochIdxOf returns the epoch index of given block number
func (s *DporSnapshot) EpochIdxOf(blockNum uint64) uint64 {
	if blockNum == 0 {
		return 0
	}
	return (blockNum - 1) / ((s.config.Epoch) * (s.config.View))
}

// FutureEpochIdxOf returns future epoch idx with given block number
func (s *DporSnapshot) FutureEpochIdxOf(blockNum uint64) uint64 {
	return s.EpochIdxOf(blockNum) + EpochGapBetweenElectionAndMining
}

// SignersOf returns signers of given block number
func (s *DporSnapshot) SignersOf(number uint64) []common.Address {
	return s.getRecentSigners(s.EpochIdxOf(number))
}

// SignerRoundOf returns signer round with given signer address and block number
func (s *DporSnapshot) SignerRoundOf(signer common.Address, number uint64) (int, error) {
	for round, s := range s.SignersOf(number) {
		if s == signer {
			return round, nil
		}
	}
	return -1, errSignerNotInCommittee
}

// IsSignerOf returns if an address is a signer in the given block number
func (s *DporSnapshot) IsSignerOf(signer common.Address, number uint64) bool {
	_, err := s.SignerRoundOf(signer, number)
	return err == nil
}

// IsLeaderOf returns if an address is a leader in the given block number
func (s *DporSnapshot) IsLeaderOf(signer common.Address, number uint64) (bool, error) {
	if number == 0 {
		return false, errGenesisBlockNumber
	}
	round, err := s.SignerRoundOf(signer, number)
	if err != nil {
		return false, err
	}
	b := round == int(((number-1)%(s.config.Epoch*s.config.View))/s.config.View)
	return b, nil
}

// FutureSignersOf returns future signers of given block number
func (s *DporSnapshot) FutureSignersOf(number uint64) []common.Address {
	return s.getRecentSigners(s.FutureEpochIdxOf(number))
}

// FutureSignerRoundOf returns the future signer round with given signer address and block number
func (s *DporSnapshot) FutureSignerRoundOf(signer common.Address, number uint64) (int, error) {
	for round, s := range s.FutureSignersOf(number) {
		if s == signer {
			return round, nil
		}
	}
	return -1, errSignerNotInCommittee
}

// IsFutureSignerOf returns if an address is a future signer in the given block number
func (s *DporSnapshot) IsFutureSignerOf(signer common.Address, number uint64) bool {
	_, err := s.FutureSignerRoundOf(signer, number)
	return err == nil
}

// InturnOf returns if a signer at a given block height is in-turn or not
func (s *DporSnapshot) InturnOf(number uint64, signer common.Address) bool {
	ok, err := s.IsLeaderOf(signer, number)
	if err != nil {
		return false
	}
	return ok
}
