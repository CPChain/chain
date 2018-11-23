package dpor

import (
	"encoding/json"
	"errors"
	"math"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"

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

	// TermDistBetweenElectionAndMining is the the term gap between election and mining.
	TermDistBetweenElectionAndMining = 2

	// MaxSizeOfRecentSigners is the size of the RecentSigners.
	// TODO: @shiyc MaxSizeOfRecentSigners is about to be removed later
	//MaxSizeOfRecentValidators is the size of the RecentValidators
	//MaxSizeOfRecentProposers is the size of the RecentProposers
	MaxSizeOfRecentSigners    = 5
	MaxSizeOfRecentValidators = 5
	MaxSizeOfRecentProposers  = 5
)

var (
	errValidatorNotInCommittee = errors.New("not a member in validators committee")
	errProposerNotInCommittee  = errors.New("not a member in proposers committee")
	errSignerNotInCommittee    = errors.New("not a member in signers committee")
	errGenesisBlockNumber      = errors.New("genesis block has no leader")
)

// Snapshot is used to check if a received block is valid by create a snapshot from previous blocks
type Snapshot interface {
	store(db database.Database) error
	copy() *Snapshot
	apply(headers []*types.Header) (*Snapshot, error)
	applyHeader(header *types.Header) error
	updateCandidates(header *types.Header) error
	updateRpts(header *types.Header) (rpt.RptList, error)
	updateSigner(rpts rpt.RptList, seed int64, viewLength int) error
	signers() []common.Address
	proposerViewOf(Signer common.Address) (int, error)
	validatorViewOf(signer common.Address) (int, error)
	signerViewOf(signer common.Address) (int, error)
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
	RecentSigners    map[uint64][]common.Address `json:"signers"`    // Set of recent signers
	RecentProposers  map[uint64][]common.Address `json:"proposers"`  // Set of recent proposers
	RecentValidators map[uint64][]common.Address `json:"validators"` // Set of recent validators

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

// TODO: @shiyc remove it later
func (s *DporSnapshot) recentSigners() map[uint64][]common.Address {
	s.lock.RLock()
	defer s.lock.RUnlock()

	recentSigners := make(map[uint64][]common.Address)
	for term, signers := range s.RecentSigners {
		recentSigners[term] = signers
	}
	return recentSigners
}

func (s *DporSnapshot) recentProposers() map[uint64][]common.Address {
	s.lock.RLock()
	defer s.lock.RUnlock()

	// copy and return proposers
	recentProposers := make(map[uint64][]common.Address)
	for term, proposers := range s.RecentProposers {
		recentProposers[term] = make([]common.Address, len(proposers))
		for i, p := range proposers {
			copy(recentProposers[term][i][:], p[:])
		}
	}
	return recentProposers
}

func (s *DporSnapshot) recentValidators() map[uint64][]common.Address {
	s.lock.RLock()
	defer s.lock.RUnlock()

	// copy and return validators
	recentValidators := make(map[uint64][]common.Address)
	for term, validators := range s.RecentValidators {
		recentValidators[term] = make([]common.Address, len(validators))
		for i, v := range validators {
			copy(recentValidators[term][i][:], v[:])
		}
	}
	return recentValidators
}

//TODO: @shiyc need to be removed later
func (s *DporSnapshot) getRecentSigners(term uint64) []common.Address {
	s.lock.RLock()
	defer s.lock.RUnlock()

	signers, ok := s.RecentSigners[term]
	if !ok {
		return nil
	}

	return signers
}

func (s *DporSnapshot) getRecentProposers(term uint64) []common.Address {
	s.lock.RLock()
	defer s.lock.RUnlock()

	signers, ok := s.RecentProposers[term]
	if !ok {
		return nil
	}

	return signers
}

func (s *DporSnapshot) getRecentValidators(term uint64) []common.Address {
	s.lock.RLock()
	defer s.lock.RUnlock()

	signers, ok := s.RecentValidators[term]
	if !ok {
		return nil
	}

	return signers
}

func (s *DporSnapshot) setRecentSigners(term uint64, signers []common.Address) {
	s.lock.Lock()
	defer s.lock.Unlock()

	ss := make([]common.Address, len(signers))
	copy(ss, signers)

	s.RecentSigners[term] = ss

	beforeTerm := uint64(math.Max(0, float64(term-MaxSizeOfRecentSigners)))
	if _, ok := s.RecentSigners[beforeTerm]; ok {
		delete(s.RecentSigners, beforeTerm)
	}

}

func (s *DporSnapshot) setRecentValidators(term uint64, validators []common.Address) {
	s.lock.Lock()
	defer s.lock.Unlock()

	ss := make([]common.Address, len(validators))
	copy(ss, validators)

	s.RecentValidators[term] = ss

	beforeTerm := uint64(math.Max(0, float64(term-MaxSizeOfRecentValidators)))
	if _, ok := s.RecentValidators[beforeTerm]; ok {
		delete(s.RecentValidators, beforeTerm)
	}

}

func (s *DporSnapshot) setRecentProposers(term uint64, proposers []common.Address) {
	s.lock.Lock()
	defer s.lock.Unlock()

	ss := make([]common.Address, len(proposers))
	copy(ss, proposers)

	s.RecentProposers[term] = ss

	beforeTerm := uint64(math.Max(0, float64(term-MaxSizeOfRecentProposers)))
	if _, ok := s.RecentProposers[beforeTerm]; ok {
		delete(s.RecentProposers, beforeTerm)
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
// method does not initialize the set of recent proposers, so only ever use if for
// the genesis block.
func newSnapshot(config *configs.DporConfig, number uint64, hash common.Hash, proposers []common.Address) *DporSnapshot {
	snap := &DporSnapshot{
		config:           config,
		Number:           number,
		Hash:             hash,
		RecentSigners:    make(map[uint64][]common.Address),
		RecentProposers:  make(map[uint64][]common.Address),
		RecentValidators: make(map[uint64][]common.Address),
	}

	// TODO: @shiyc need to remove setRecentSigners(), and consider whether we need setRecentValidators()
	snap.setRecentSigners(snap.Term(), proposers)
	snap.setRecentProposers(snap.Term(), proposers)
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
		config:           s.config,
		Number:           s.number(),
		Hash:             s.hash(),
		Candidates:       make([]common.Address, len(s.Candidates)),
		RecentSigners:    make(map[uint64][]common.Address),
		RecentValidators: make(map[uint64][]common.Address),
		RecentProposers:  make(map[uint64][]common.Address),
	}

	copy(cpy.Candidates, s.candidates())
	for term, signers := range s.recentSigners() {
		cpy.setRecentSigners(term, signers)
	}
	for term, proposer := range s.recentProposers() {
		cpy.setRecentSigners(term, proposer)
	}
	for term, validator := range s.recentValidators() {
		cpy.setRecentSigners(term, validator)
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

	return snap, nil
}

// applyHeader applies header to Snapshot to calculate reputations of candidates fetched from candidate contract
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
	if IsCheckPoint(s.number(), s.config.TermLen, s.config.ViewLen) {
		seed := header.Hash().Big().Int64()
		s.updateProposers(rpts, seed)
	}

	return nil
}

// updateCandidates updates proposer candidates from campaign contract
func (s *DporSnapshot) updateCandidates(header *types.Header) error {
	contractCaller := s.contractCaller()

	var candidates []common.Address
	// If contractCaller is not nil, use it to update candidates from contract
	if contractCaller != nil {

		// Creates an contract instance
		campaignAddress := s.config.Contracts["campaign"]
		contractInstance, err := campaign.NewCampaign(campaignAddress, contractCaller.Client)
		if err != nil {
			return err
		}

		// Read candidates from the contract instance
		cds, err := contractInstance.CandidatesOf(nil, big.NewInt(1))
		if err != nil {
			return err
		}

		// If useful, use it!
		if uint64(len(cds)) > s.config.TermLen {
			candidates = cds
		}
	}

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

// isUseDefaultProposers returns true if it should use predefined default proposers, otherwise false
func (s *DporSnapshot) isUseDefaultProposers() bool {
	return s.Number <= s.config.MaxInitBlockNumber
}

func (s *DporSnapshot) isStartElection() bool {
	return s.number() >= s.config.MaxInitBlockNumber-(TermDistBetweenElectionAndMining*s.config.TermLen*s.config.ViewLen)-1
}

// updateProposer uses rpt and election result to get new proposers committee
func (s *DporSnapshot) updateProposers(rpts rpt.RptList, seed int64) {
	// Elect proposers
	if s.isStartElection() {
		log.Debug("electing")
		log.Debug("---------------------------")
		log.Debug("rpts:")
		for _, r := range rpts {
			log.Debug("rpt:", "addr", r.Address.Hex(), "rpt value", r.Rpt)
		}
		log.Debug("seed", "seed", seed)
		log.Debug("term length", "term", int(s.config.TermLen))
		log.Debug("---------------------------")

		proposers := election.Elect(rpts, seed, int(s.config.TermLen))

		log.Debug("elected proposers:")

		for _, s := range proposers {
			log.Debug("proposer", "addr", s.Hex())
		}
		log.Debug("---------------------------")

		log.Debug("snap.number", "n", s.number())

		term := s.FutureTermOf(s.number())

		log.Debug("term idx", "eidx", term)

		s.setRecentProposers(term, proposers)

		log.Debug("---------------------------")
		proposers = s.getRecentProposers(term)
		log.Debug("stored elected proposers")

		for _, s := range proposers {
			log.Debug("proposer", "addr", s.Hex())
		}
		log.Debug("---------------------------")

	}

	// Set default proposer if it is in initial stage
	if s.isUseDefaultProposers() {
		// Use default proposers
		proposers := s.candidates()[:s.config.TermLen]
		s.setRecentProposers(s.Term()+1, proposers)
	}

	return
}

// Term returns the term index of current block number, which is 0-based
func (s *DporSnapshot) Term() uint64 {
	return s.TermOf(s.number())
}

// TermOf returns the term index of given block number
func (s *DporSnapshot) TermOf(blockNum uint64) uint64 {
	return blockNum / ((s.config.TermLen) * (s.config.ViewLen))
}

// FutureTermOf returns future term idx with given block number
func (s *DporSnapshot) FutureTermOf(blockNum uint64) uint64 {
	return s.TermOf(blockNum) + TermDistBetweenElectionAndMining
}

// SignersOf returns signers of given block number
// TODO: @shiyc need to be removed later
func (s *DporSnapshot) SignersOf(number uint64) []common.Address {
	return s.getRecentSigners(s.TermOf(number))
}

func (s *DporSnapshot) ValidatorsOf(number uint64) []common.Address {
	return s.getRecentValidators(s.TermOf(number))
}

func (s *DporSnapshot) ProposersOf(number uint64) []common.Address {
	return s.getRecentProposers(s.TermOf(number))
}

// ValidatorViewOf returns validator's view with given validator's address and block number
func (s *DporSnapshot) ValidatorViewOf(validator common.Address, number uint64) (int, error) {
	for view, s := range s.ValidatorsOf(number) {
		if s == validator {
			return view, nil
		}
	}
	return -1, errValidatorNotInCommittee
}

// ProposerViewOf returns the proposer's view with given proposer's address and block number
func (s *DporSnapshot) ProposerViewOf(proposer common.Address, number uint64) (int, error) {
	for view, s := range s.ProposersOf(number) {
		if s == proposer {
			return view, nil
		}
	}
	return -1, errProposerNotInCommittee
}

// SignerViewOf returns signer view with given signer address and block number
func (s *DporSnapshot) SignerViewOf(signer common.Address, number uint64) (int, error) {
	for view, s := range s.SignersOf(number) {
		if s == signer {
			return view, nil
		}
	}
	return -1, errSignerNotInCommittee
}

// IsValidatorOf returns if an address is a validator in the given block number
func (s *DporSnapshot) IsValidatorOf(validator common.Address, number uint64) bool {
	_, err := s.ValidatorViewOf(validator, number)
	return err == nil
}

// IsSignerOf returns if an address is a signer in the given block number
// TODO: @shiyc need to removed later
func (s *DporSnapshot) IsSignerOf(signer common.Address, number uint64) bool {
	_, err := s.SignerViewOf(signer, number)
	return err == nil
}

// IsLeaderOf returns if an address is the leader of the validators committee
// It is invoked only in the scenario when impeachment is activated
func (s *DporSnapshot) IsLeaderOf(signer common.Address, number uint64) (bool, error) {
	if number == 0 {
		return false, errGenesisBlockNumber
	}
	view, err := s.ProposerViewOf(signer, number)
	if err != nil {
		return false, err
	}
	b := view == int(((number-1)%(s.config.TermLen*s.config.ViewLen))/s.config.ViewLen)
	return b, nil
	//TODO: @shiyc finish it during the implement of impeachment
	return false, nil
}

// IsProposerOf returns if an address is a proposer in the given block number
func (s *DporSnapshot) IsProposerOf(signer common.Address, number uint64) (bool, error) {
	if number == 0 {
		return false, errGenesisBlockNumber
	}
	view, err := s.ProposerViewOf(signer, number)
	if err != nil {
		return false, err
	}
	b := view == int(((number-1)%(s.config.TermLen*s.config.ViewLen))/s.config.ViewLen)
	return b, nil
}

// FutureSignersOf returns future signers of given block number
func (s *DporSnapshot) FutureSignersOf(number uint64) []common.Address {
	return s.getRecentSigners(s.FutureTermOf(number))
}

// FutureProposersOf returns future proposers of given block number
func (s *DporSnapshot) FutureProposersOf(number uint64) []common.Address {
	return s.getRecentProposers(s.FutureTermOf(number))
}

// FutureSignerViewOf returns the future signer view with given signer address and block number
// TODO: @shiyc need to remove it later
func (s *DporSnapshot) FutureSignerViewOf(signer common.Address, number uint64) (int, error) {
	for view, s := range s.FutureSignersOf(number) {
		if s == signer {
			return view, nil
		}
	}
	return -1, errSignerNotInCommittee
}

// FutureProposerViewOf returns the future signer view with given signer address and block number
func (s *DporSnapshot) FutureProposerViewOf(signer common.Address, number uint64) (int, error) {
	for view, s := range s.FutureProposersOf(number) {
		if s == signer {
			return view, nil
		}
	}
	return -1, errValidatorNotInCommittee
}

// IsFutureSignerOf returns if an address is a future signer in the given block number
// TODO: @shiyc need to remove it later
func (s *DporSnapshot) IsFutureSignerOf(signer common.Address, number uint64) bool {
	_, err := s.FutureSignerViewOf(signer, number)
	return err == nil
}

//IsFutureProposerOf returns if an address is a future proposer in the given block number
func (s *DporSnapshot) IsFutureProposerOf(proposer common.Address, number uint64) bool {
	_, err := s.FutureProposerViewOf(proposer, number)
	return err == nil
}

// InturnOf returns if a signer at a given block height is in-turn or not
func (s *DporSnapshot) InturnOf(number uint64, signer common.Address) bool {
	ok, err := s.IsProposerOf(signer, number)
	if err != nil {
		return false
	}
	return ok
}

func (s *DporSnapshot) StartBlockNumberOfTerm(term uint64) uint64 {
	return s.config.ViewLen * s.config.TermLen * term
}
