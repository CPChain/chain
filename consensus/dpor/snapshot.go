package dpor

import (
	"encoding/json"
	"errors"
	"fmt"
	"math"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/consensus/dpor/election"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"
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
	MaxSizeOfRecentSigners    = 200
	MaxSizeOfRecentValidators = 200
	MaxSizeOfRecentProposers  = 200
)

var (
	errValidatorNotInCommittee = errors.New("not a member in validators committee")
	errProposerNotInCommittee  = errors.New("not a member in proposers committee")
	errSignerNotInCommittee    = errors.New("not a member in signers committee")
	errGenesisBlockNumber      = errors.New("genesis block has no leader")
	errInsufficientCandidates  = errors.New("insufficient candidates")
)

// DporSnapshot is the state of the authorization voting at a given point in time.
type DporSnapshot struct {
	Mode       Mode             `json:"mode"`
	Number     uint64           `json:"number"`     // Block number where the Snapshot was created
	Hash       common.Hash      `json:"hash"`       // Block hash where the Snapshot was created
	Candidates []common.Address `json:"candidates"` // Set of candidates read from campaign contract
	// RecentSigners *lru.ARCCache    `json:"signers"`
	RecentSigners    map[uint64][]common.Address `json:"signers"`    // Set of recent signers
	RecentProposers  map[uint64][]common.Address `json:"proposers"`  // Set of recent proposers
	RecentValidators map[uint64][]common.Address `json:"validators"` // Set of recent validators

	config     *configs.DporConfig   // Consensus engine parameters to fine tune behavior
	Client     backend.ClientBackend `json:"-"`
	rptBackend rpt.RptService

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
		log.Warn("proposers for the term not exist", "term", term)
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

func (s *DporSnapshot) client() backend.ClientBackend {
	s.lock.RLock()
	defer s.lock.RUnlock()

	return s.Client
}

func (s *DporSnapshot) setClient(client backend.ClientBackend) {
	s.lock.Lock()
	defer s.lock.Unlock()

	s.Client = client
}

// newSnapshot creates a new Snapshot with the specified startup parameters. This
// method does not initialize the set of recent proposers, so only ever use if for
// the genesis block.
func newSnapshot(config *configs.DporConfig, number uint64, hash common.Hash, proposers []common.Address,
	validators []common.Address, mode Mode) *DporSnapshot {
	snap := &DporSnapshot{
		Mode:             mode,
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
	snap.setRecentValidators(snap.Term(), validators)
	return snap
}

// loadSnapshot loads an existing Snapshot from the database.
func loadSnapshot(config *configs.DporConfig, client backend.ClientBackend, rpt rpt.RptService, db database.Database,
	hash common.Hash) (*DporSnapshot, error) {

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
	snap.Client = client
	snap.rptBackend = rpt

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
		cpy.setRecentProposers(term, proposer)
	}
	for term, validator := range s.recentValidators() {
		cpy.setRecentValidators(term, validator)
	}
	cpy.rptBackend = s.rptBackend
	return cpy
}

// apply creates a new authorization Snapshot by applying the given headers to
// the original one.
func (s *DporSnapshot) apply(headers []*types.Header, client backend.ClientBackend) (*DporSnapshot, error) {
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
	snap.setClient(client)
	log.Info("apply headers", "len(headers)", len(headers))
	for _, header := range headers {
		err := snap.applyHeader(header)
		if err != nil {
			log.Warn("DporSnapshot apply header error.", "err", err)
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
	err := s.updateCandidates()
	if err != nil {
		log.Warn("err when update candidates", "err", err)
		return err
	}

	// Update rpts
	rpts, err := s.updateRpts()
	if err != nil {
		log.Warn("err when update rpts", "err", err)
		return err
	}

	// If in checkpoint, run election
	if IsCheckPoint(s.number(), s.config.TermLen, s.config.ViewLen) {
		seed := header.Hash().Big().Int64()
		s.updateProposers(rpts, seed)
	}

	term := s.TermOf(header.Number.Uint64())
	if len(header.Dpor.Validators) != 0 && len(header.Dpor.Validators) > 4 { // 3f + 1, TODO: @AC add a config
		s.setRecentValidators(term+1, header.Dpor.Validators)
	} else if IsCheckPoint(header.Number.Uint64(), s.config.TermLen, s.config.ViewLen) {
		s.setRecentValidators(term+1, s.getRecentValidators(term))
	}

	return nil
}

// updateCandidates updates proposer candidates from campaign contract
func (s *DporSnapshot) updateCandidates() error {

	var candidates []common.Address

	if s.Mode == NormalMode && s.isStartElection() {
		client := s.client()
		// If contractCaller is not nil, use it to update candidates from contract
		if client != nil {
			// Creates an contract instance
			campaignAddress := s.config.Contracts[configs.ContractCampaign]
			log.Info("campaignAddress", "addr", campaignAddress.Hex())
			contractInstance, err := campaign.NewCampaign(campaignAddress, client)
			if err != nil {
				log.Error("new Campaign error", err)
				return err
			}

			term := s.TermOf(s.Number)
			// Read candidates from the contract instance
			cds, err := contractInstance.CandidatesOf(nil, new(big.Int).SetUint64(term))
			if err != nil {
				log.Error("read Candidates error, use default candidates instead", "err", err)
				// use default candidates instead
				s.setCandidates(configs.Candidates())
				return nil // swallow the error as it has been handled properly
			}

			log.Info("got candidates from contract of term", "len(candidates)", len(cds), "term", term)

			// If useful, use it!
			if uint64(len(cds)) >= s.config.TermLen {
				candidates = cds
			}
		}
	}

	if uint64(len(candidates)) < s.config.TermLen {
		log.Debug("no enough candidates,use default candidates")
		candidates = configs.Candidates()
	}

	log.Info("set candidates", "len(candidates)", len(candidates))
	for i, c := range candidates {
		log.Info(fmt.Sprintf("candidate #%d", i), "candidate", c.Hex())
	}

	s.setCandidates(candidates)
	return nil
}

// updateRpts updates rpts of candidates
func (s *DporSnapshot) updateRpts() (rpt.RptList, error) {

	if s.client() == nil && s.Mode == NormalMode {
		log.Warn("snapshot contract caller is nil")
		s.Mode = FakeMode
	}

	switch {
	case s.Mode == NormalMode && s.isStartElection():

		rptBackend, err := s.rptBackend, error(nil)
		if rptBackend == nil {
			rptBackend, err = rpt.NewRptService(s.client(), s.config.Contracts[configs.ContractRpt])
		}
		// rpts := rptBackend.CalcRptInfoList(s.candidates(), s.number())
		cs := s.candidates()
		rpts := make(rpt.RptList, len(cs))
		for i, c := range cs {
			rpts[i] = rpt.Rpt{Address: c, Rpt: 100}
		}

		s.rptBackend = rptBackend

		return rpts, err
	default:
		var rpts rpt.RptList
		for idx, candidate := range s.candidates() {
			r := rpt.Rpt{Address: candidate, Rpt: int64(idx)}
			rpts = append(rpts, r)
		}

		return rpts, nil
	}
}

// isUseDefaultProposers returns true if it should use predefined default proposers, otherwise false
func (s *DporSnapshot) isUseDefaultProposers() bool {
	return s.Number <= s.config.MaxInitBlockNumber
}

func (s *DporSnapshot) isStartElection() bool {
	return s.number() >= s.config.MaxInitBlockNumber-(TermDistBetweenElectionAndMining*s.config.TermLen*s.config.ViewLen)
}

// updateProposer uses rpt and election result to get new proposers committee
func (s *DporSnapshot) updateProposers(rpts rpt.RptList, seed int64) {
	// Elect proposers
	if s.isStartElection() {
		log.Info("electing")
		log.Info("---------------------------")
		log.Info("rpts:")
		for _, r := range rpts {
			log.Info("rpt:", "addr", r.Address.Hex(), "rpt value", r.Rpt)
		}
		log.Info("seed", "seed", seed)
		log.Info("term length", "term", int(s.config.TermLen))
		log.Info("---------------------------")

		proposers := election.Elect(rpts, seed, int(s.config.TermLen))

		log.Info("elected proposers:")

		for _, s := range proposers {
			log.Info("proposer", "addr", s.Hex())
		}
		log.Info("---------------------------")

		log.Info("snap.number", "n", s.number())

		term := s.FutureTermOf(s.number())

		log.Debug("term idx", "eidx", term)

		s.setRecentProposers(term, proposers)

		log.Info("---------------------------")
		proposers = s.getRecentProposers(term)
		log.Info("stored elected proposers")

		for _, s := range proposers {
			log.Info("proposer", "addr", s.Hex())
		}
		log.Info("---------------------------")

		if uint64(len(proposers)) != s.config.TermLen {
			log.Warn("proposer length wrong", "expect", s.config.TermLen, "actual", len(proposers))
			log.Warn("---------- proposers --------")
			for _, s := range proposers {
				log.Warn("proposer", "addr", s.Hex())
			}
		}
	}

	// Set default proposer if it is in initial stage
	if s.isUseDefaultProposers() {
		// Use default proposers
		proposers := s.candidates()[:s.config.TermLen]
		s.setRecentProposers(s.Term()+1, proposers)
		log.Info("use default proposers", "term", s.Term()+1, "proposers", len(proposers))
		for i, p := range proposers {
			log.Info(fmt.Sprintf("proposer #%d details", i), "address", p.Hex())
		}
	}

	return
}

// Term returns the term index of current block number, which is 0-based
func (s *DporSnapshot) Term() uint64 {
	return s.TermOf(s.number())
}

// TermOf returns the term index of given block number
func (s *DporSnapshot) TermOf(blockNum uint64) uint64 {
	if blockNum == 0 {
		return 0 // block number 0 is a special case, its term is set to 0
	}
	return (blockNum - 1) / ((s.config.TermLen) * (s.config.ViewLen))
}

// FutureTermOf returns future term idx with given block number
func (s *DporSnapshot) FutureTermOf(blockNum uint64) uint64 {
	return s.TermOf(blockNum) + TermDistBetweenElectionAndMining + 1
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

// ProposerViewOf returns the proposer's view(turn) with given proposer's address and block number
func (s *DporSnapshot) ProposerViewOf(proposer common.Address, number uint64) (int, error) {
	for view, s := range s.ProposersOf(number) {
		if s == proposer {
			return view, nil
		}
	}
	return -1, errProposerNotInCommittee
}

// IsValidatorOf returns if an address is a validator in the given block number
func (s *DporSnapshot) IsValidatorOf(validator common.Address, number uint64) bool {
	_, err := s.ValidatorViewOf(validator, number)
	return err == nil
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
