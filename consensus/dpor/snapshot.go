package dpor

import (
	"encoding/json"
	"errors"
	"math"
	"sync"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/consensus/dpor/election"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

const (

	// EpochGapBetweenElectionAndMining is the the epoch gap between election and mining.
	EpochGapBetweenElectionAndMining = 3

	// MaxSizeOfRecentSigners is the size of the RecentSigners.
	MaxSizeOfRecentSigners = 5
)

var (
	errSignerNotInCommittee = errors.New("signer not in committee")
	errGenesisBlockNumber   = errors.New("genesis block has no leader")
)

// Snapshot is used to check if a received block is valid by create a snapshot from previous blocks
type Snapshot interface {
	store(db database.Database) error
	copy() *Snapshot
	apply(headers []*types.Header) (*Snapshot, error)
	applyHeader(header *types.Header) error
	updateCandidates(header *types.Header) error
	updateRpts(header *types.Header) (rpt.RptList, error)
	updateView(rpts rpt.RptList, seed int64, viewLength int) error
	signers() []common.Address
	signerRound(signer common.Address) (int, error)
	isSigner(signer common.Address) bool
	isLeader(signer common.Address, number uint64) (bool, error)
	candidates() []common.Address
	inturn(number uint64, signer common.Address) bool
}

// DporSnapshot is the state of the authorization voting at a given point in time.
type DporSnapshot struct {
	Number     uint64           `json:"number"`     // Block number where the Snapshot was created
	Hash       common.Hash      `json:"hash"`       // Block hash where the Snapshot was created
	Candidates []common.Address `json:"candidates"` // Set of candidates read from campaign contract
	// RecentSigners *lru.ARCCache    `json:"signers"`
	RecentSigners map[uint64][]common.Address `json:"signers"` // Set of recent signers

	config         *configs.DporConfig // Consensus engine parameters to fine tune behavior
	ContractCaller *backend.ContractCaller

	lock sync.RWMutex
}

func (s *DporSnapshot) number() uint64 {
	s.lock.RLock()
	defer s.lock.RUnlock()

	number := s.Number
	return number
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
	s.lock.RLock()
	defer s.lock.RUnlock()

	hash := s.Hash
	return hash
}

func (s *DporSnapshot) candidates() []common.Address {
	s.lock.RLock()
	defer s.lock.RUnlock()

	candidates := s.Candidates
	return candidates
}

func (s *DporSnapshot) setCandidates(candidates []common.Address) {
	s.lock.Lock()
	defer s.lock.Unlock()

	cands := make([]common.Address, len(candidates))
	copy(cands, candidates)

	s.Candidates = cands
}

func (s *DporSnapshot) recentSigners() map[uint64][]common.Address {
	s.lock.RLock()
	defer s.lock.RUnlock()

	recentSigners := make(map[uint64][]common.Address)
	for epochIdx, signers := range s.RecentSigners {
		recentSigners[epochIdx] = signers
	}
	return recentSigners
}

func (s *DporSnapshot) getRecentSigners(epochIdx uint64) []common.Address {
	s.lock.RLock()
	defer s.lock.RUnlock()

	signers, ok := s.RecentSigners[epochIdx]
	if !ok {
		return nil
	}

	return signers
}

func (s *DporSnapshot) setRecentSigners(epochIdx uint64, signers []common.Address) {
	s.lock.Lock()
	defer s.lock.Unlock()

	ss := make([]common.Address, len(signers))
	copy(ss, signers)
	s.RecentSigners[epochIdx] = ss

	beforeEpochIdx := uint64(math.Max(0, float64(epochIdx-MaxSizeOfRecentSigners)))
	if _, ok := s.RecentSigners[beforeEpochIdx]; ok {
		delete(s.RecentSigners, beforeEpochIdx)
	}

}

func (s *DporSnapshot) contractCaller() *backend.ContractCaller {
	s.lock.RLock()
	defer s.lock.RUnlock()

	return s.ContractCaller
}

func (s *DporSnapshot) setContractCaller(contractCaller *backend.ContractCaller) {
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
func loadSnapshot(config *configs.DporConfig, db database.Database, hash common.Hash) (*DporSnapshot, error) {

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
func (s *DporSnapshot) store(db database.Database) error {
	s.lock.Lock()
	defer s.lock.Unlock()

	blob, err := json.Marshal(s)
	if err != nil {
		return err
	}
	return db.Put(append([]byte("dpor-"), s.Hash[:]...), blob)
}

// copy creates a deep copy of the Snapshot, though not the individual votes.
func (s *DporSnapshot) copy() *DporSnapshot {
	cpy := &DporSnapshot{
		config:        s.config,
		Number:        s.number(),
		Hash:          s.hash(),
		Candidates:    make([]common.Address, len(s.Candidates)),
		RecentSigners: make(map[uint64][]common.Address),
	}

	copy(cpy.Candidates, s.candidates())
	for epochIdx, signers := range s.recentSigners() {
		cpy.setRecentSigners(epochIdx, signers)
	}

	return cpy
}

// apply creates a new authorization Snapshot by applying the given headers to
// the original one.
func (s *DporSnapshot) apply(headers []*types.Header, contractCaller *backend.ContractCaller) (*DporSnapshot, error) {
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
		common.HexToAddress("0x6e31e5b68a98dcd17264bd1ba547d0b3e874da1e"),
		common.HexToAddress("0x22a672eab2b1a3ff3ed91563205a56ca5a560e08"),
		common.HexToAddress("0x7b2f052a372951d02798853e39ee56c895109992"),
		common.HexToAddress("0x2f0176cc3a8617b6ddea6a501028fa4c6fc25ca1"),
		common.HexToAddress("0xe4d51117832e84f1d082e9fc12439b771a57e7b2"),
		common.HexToAddress("0x32bd7c33bb5060a85f361caf20c0bda9075c5d51"),
	}

	// contractCaller := s.contractCaller()

	// If contractCaller is not nil, use it to update candidates from contract
	// if contractCaller != nil {

	// 	// Creates an contract instance
	// 	campaignAddress := s.config.Contracts["campaign"]
	// 	contractInstance, err := contract.NewCampaign(campaignAddress, contractCaller.Client)
	// 	if err != nil {
	// 		return err
	// 	}

	// 	// Read candidates from the contract instance
	// 	cds, err := contractInstance.CandidatesOf(nil, big.NewInt(1))
	// 	if err != nil {
	// 		return err
	// 	}

	// 	// If useful, use it!
	// 	if uint64(len(cds)) > s.config.Epoch {
	// 		candidates = cds
	// 	}
	// }

	s.setCandidates(candidates)
	return nil
}

// updateRpts updates rpts of candidates
func (s *DporSnapshot) updateRpts(header *types.Header) (rpt.RptList, error) {

	// TODO: use rpt collector to update rpts.
	var rpts rpt.RptList
	for idx, candidate := range s.candidates() {
		r := rpt.Rpt{Address: candidate, Rpt: int64(idx)}
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
func (s *DporSnapshot) updateSigners(rpts rpt.RptList, seed int64) error {

	signers := s.candidates()[:s.config.Epoch]

	// Use default signers
	if s.ifUseDefaultSigners() {
		s.setRecentSigners(s.EpochIdx()+1, signers)
	}

	// Elect signers
	if s.ifStartElection() {
		log.Debug("electing")
		log.Debug(",,,,,,,,,,,,,,,,,,,,,,,,,,,")
		log.Debug("rpts:")
		for _, r := range rpts {
			log.Debug("rpt:", "addr", r.Address.Hex(), "rpt value", r.Rpt)
		}
		log.Debug("seed", "seed", seed)
		log.Debug("epoch length", "epoch", int(s.config.Epoch))
		log.Debug(",,,,,,,,,,,,,,,,,,,,,,,,,,,")

		signers := election.Elect(rpts, seed, int(s.config.Epoch))

		log.Debug("elected signers:")

		for _, s := range signers {
			log.Debug("signer", "addr", s.Hex())
		}
		log.Debug(",,,,,,,,,,,,,,,,,,,,,,,,,,,")

		log.Debug("snap.number", "n", s.number())

		epochIdx := s.FutureEpochIdxOf(s.number())

		log.Debug("epoch idx", "eidx", epochIdx)

		s.setRecentSigners(epochIdx, signers)

		log.Debug(",,,,,,,,,,,,,,,,,,,,,,,,,,,")
		signers = s.getRecentSigners(epochIdx)
		log.Debug("stored elected signers")

		for _, s := range signers {
			log.Debug("signer", "addr", s.Hex())
		}
		log.Debug(",,,,,,,,,,,,,,,,,,,,,,,,,,,")

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
