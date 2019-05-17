package dpor

import (
	"encoding/json"
	"errors"
	"fmt"
	"math"
	"math/rand"
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

	// TermDistBetweenElectionAndMining is the the term gap between election and mining.
	TermDistBetweenElectionAndMining = 2 // TermDistBetweenElectionAndMining = effective term - current term(last block)

	//MaxSizeOfRecentValidators is the size of the RecentValidators
	MaxSizeOfRecentValidators = 200

	//MaxSizeOfRecentProposers is the size of the RecentProposers
	MaxSizeOfRecentProposers = 200
)

const defaultProposersNum = 4

var (
	errValidatorNotInCommittee = errors.New("not a member in validators committee")
	errProposerNotInCommittee  = errors.New("not a member in proposers committee")
	errSignerNotInCommittee    = errors.New("not a member in signers committee")
	errGenesisBlockNumber      = errors.New("genesis block has no leader")
	errInsufficientCandidates  = errors.New("insufficient candidates")
)

// DporSnapshot is the state of the authorization voting at a given point in time.
type DporSnapshot struct {
	Mode             Mode                        `json:"mode"`
	Number           uint64                      `json:"number"`     // Block number where the Snapshot was created
	Hash             common.Hash                 `json:"hash"`       // Block hash where the Snapshot was created
	Candidates       []common.Address            `json:"candidates"` // Set of candidates read from campaign contract
	RecentProposers  map[uint64][]common.Address `json:"proposers"`  // Set of recent proposers
	RecentValidators map[uint64][]common.Address `json:"validators"` // Set of recent validators

	config *configs.DporConfig // Consensus engine parameters to fine tune behavior

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

func (s *DporSnapshot) getRecentProposers(term uint64) []common.Address {
	s.lock.RLock()
	defer s.lock.RUnlock()

	signers, ok := s.RecentProposers[term]
	if !ok {
		log.Debug("proposers for the term not exist", "term", term)
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
		RecentProposers:  make(map[uint64][]common.Address),
		RecentValidators: make(map[uint64][]common.Address),
	}

	snap.setRecentProposers(snap.Term(), proposers)
	snap.setRecentValidators(snap.Term(), validators)
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
		RecentValidators: make(map[uint64][]common.Address),
		RecentProposers:  make(map[uint64][]common.Address),
	}

	copy(cpy.Candidates, s.candidates())
	for term, proposer := range s.recentProposers() {
		cpy.setRecentProposers(term, proposer)
	}
	for term, validator := range s.recentValidators() {
		cpy.setRecentValidators(term, validator)
	}
	return cpy
}

// apply creates a new authorization Snapshot by applying the given headers to
// the original one.
func (s *DporSnapshot) apply(headers []*types.Header, timeToUpdateCommitttee bool, candidateService rpt.CandidateService, rptService rpt.RptService) (*DporSnapshot, error) {
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
	log.Debug("apply headers", "len(headers)", len(headers))
	for _, header := range headers {

		// TODO: write a function to do this
		ifUpdateCommittee := timeToUpdateCommitttee

		err := snap.applyHeader(header, ifUpdateCommittee, candidateService, rptService)
		if err != nil {
			log.Warn("DporSnapshot apply header error.", "err", err)
			return nil, err
		}
	}

	return snap, nil
}

// applyHeader applies header to Snapshot to calculate reputations of candidates fetched from candidate contract
func (s *DporSnapshot) applyHeader(header *types.Header, ifUpdateCommittee bool, candidateService rpt.CandidateService, rptService rpt.RptService) error {
	// Update Snapshot attributes.
	s.setNumber(header.Number.Uint64())
	s.setHash(header.Hash())

	// When ifUpdateCommittee is true, update candidates, rpts, and run election if necessary
	if ifUpdateCommittee {

		// Update candidates
		log.Debug("start updating candidates")
		err := s.updateCandidates(candidateService)
		if err != nil {
			log.Warn("err when update candidates", "err", err)
			return err
		}
		log.Debug("candidates updated", "len(candidates)", len(s.candidates()), "number", s.number())
		for i, c := range s.candidates() {
			log.Debug(fmt.Sprintf("candiate #%d", i), "addr", c.Hex())
		}

		// Update rpts
		log.Debug("start updating rpts")
		rpts, err := s.updateRpts(rptService)
		if err != nil {
			log.Warn("err when update rpts", "err", err)
			return err
		}
		log.Debug("rpts updated", "len(rpts)", len(rpts), "number", s.number())
		for i, r := range rpts {
			log.Debug(fmt.Sprintf("rpt #%d", i), "addr", r.Address.Hex(), "score", r.Rpt)
		}

		// If in checkpoint, run election
		if backend.IsCheckPoint(s.number(), s.config.TermLen, s.config.ViewLen) {
			log.Debug("update proposers committee", "number", s.number())
			seed := header.Hash().Big().Int64()
			s.updateProposers(rpts, seed, rptService)
		}

	}

	term := s.TermOf(header.Number.Uint64())
	if len(header.Dpor.Validators) != 0 && len(header.Dpor.Validators) == int(s.config.ValidatorsLen()) {
		// TODO: there is a vulnerability about validators in header, check it!
		// for now, i just do not update validators from header.
		// s.setRecentValidators(term+1, header.Dpor.Validators)
	} else if backend.IsCheckPoint(header.Number.Uint64(), s.config.TermLen, s.config.ViewLen) {
		s.setRecentValidators(term+1, s.getRecentValidators(term))
	}

	return nil
}

// updateCandidates updates proposer candidates from campaign contract
func (s *DporSnapshot) updateCandidates(candidateService rpt.CandidateService) error {
	var candidates []common.Address

	if s.Mode == NormalMode && s.isStartElection() && candidateService != nil {

		// Read candidates from the contract instance
		term := s.TermOf(s.Number)
		cds, err := candidateService.CandidatesOf(term)
		if err != nil {
			log.Error("read Candidates error, use default candidates instead", "err", err)
			// use default candidates instead
			s.setCandidates(configs.Candidates())
			return nil // swallow the error as it has been handled properly
		}

		log.Debug("got candidates from contract of term", "num", s.Number, "len(candidates)", len(cds), "term", term)

		// If useful, use it!
		if uint64(len(cds)) >= s.config.TermLen {
			candidates = cds
		}
	}

	// not enough candidates, use default candidates
	if uint64(len(candidates)) < s.config.TermLen {
		log.Debug("no enough candidates,use default candidates")
		candidates = configs.Candidates()
	}

	// too many candidates
	if len(candidates) > configs.MaximumCandidateNumber {
		log.Debug("candidates is more than max allowed", "max", configs.MaximumCandidateNumber, "len", len(candidates))
		candidates = candidates[:configs.MaximumCandidateNumber]
	}

	log.Debug("set candidates", "len(candidates)", len(candidates))
	for i, c := range candidates {
		log.Debug(fmt.Sprintf("candidate #%d", i), "candidate", c.Hex())
	}

	s.setCandidates(candidates)
	return nil
}

// TODO: do not update rpts on every block
// updateRpts updates rpts of candidates
func (s *DporSnapshot) updateRpts(rptService rpt.RptService) (rpt.RptList, error) {

	switch {
	case s.Mode == NormalMode && s.isStartElection() && rptService != nil:
		rpts := rptService.CalcRptInfoList(s.candidates(), s.number())
		log.Debug("called contract to get rpts", "rpts", rpts.FormatString())
		return rpts, nil
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

func (s *DporSnapshot) isStartCampaign() bool {
	return s.number() >= s.config.MaxInitBlockNumber-((TermDistBetweenElectionAndMining+1)*s.config.TermLen*s.config.ViewLen)
}

// isAboutToCampaign returns a bool value indicating when it is about (1 round in advance) to campaign
func (s *DporSnapshot) isAboutToCampaign() bool {
	return s.number() >= s.config.MaxInitBlockNumber-((TermDistBetweenElectionAndMining+2)*s.config.TermLen*s.config.ViewLen)
}

// updateProposer uses rpt and election result to get new proposers committee
func (s *DporSnapshot) updateProposers(rpts rpt.RptList, seed int64, rptService rpt.RptService) {
	// Elect proposers
	if s.isStartElection() {

		// some logs about rpt infos
		log.Debug("---------------------------")
		log.Debug("start election")
		log.Debug("rpts list:")
		for idx, r := range rpts {
			log.Debug("rpt:", "idx", idx, "addr", r.Address.Hex(), "value", r.Rpt)
		}
		log.Debug("seed", "seed", seed)
		log.Debug("term length", "term", int(s.config.TermLen))
		log.Debug("---------------------------")

		// run the election algorithm
		var proposers []common.Address
		if int(s.config.TermLen) > defaultProposersNum {

			// some logs
			log.Debug("---------------------------")
			log.Debug("default 12 proposers")
			for i, ep := range configs.Proposers() {
				log.Debug("proposer", "idx", i, "addr", ep.Hex())
			}
			log.Debug("---------------------------")

			// elect some proposers based on rpts
			randomSlots, _ := rptService.RandomLevel()
			electedProposers := election.Elect(rpts, seed, randomSlots)

			// some logs
			log.Debug("---------------------------")
			log.Debug("elected proposers", "num", randomSlots)
			for i, ep := range electedProposers {
				log.Debug("proposer", "idx", i, "addr", ep.Hex())
			}
			log.Debug("---------------------------")

			// append default proposers to the end of electedProposers
			defaultSlots := int(s.config.TermLen) - randomSlots - defaultProposersNum
			for _, addr := range configs.Proposers()[:defaultSlots] {
				log.Debug("append default proposer to elected proposers", "addr", addr.Hex())
				electedProposers = append(electedProposers, addr)
			}

			// chose some default proposers
			chosenProposers := choseSomeProposers(configs.Proposers(), seed, defaultProposersNum)

			// some logs
			log.Debug("---------------------------")
			log.Debug("chosen 4 proposers")
			for i, ep := range chosenProposers {
				log.Debug("proposer", "idx", i, "addr", ep.Hex())
			}
			log.Debug("---------------------------")

			// combine together
			proposers = evenlyInsertDefaultProposers(electedProposers, chosenProposers, seed, int(s.config.TermLen))

			// some logs
			log.Debug("---------------------------")
			log.Debug("evenly spared 12 proposers")
			for i, ep := range proposers {
				log.Debug("proposer", "idx", i, "addr", ep.Hex())
			}
			log.Debug("---------------------------")

		} else {
			proposers = election.Elect(rpts, seed, int(s.config.TermLen))
		}

		if len(proposers) != int(s.config.TermLen) {
			panic("invalid length of prepared proposer list")
		}

		// save to cache
		term := s.FutureTermOf(s.number())
		s.setRecentProposers(term, proposers)

		// some logs about elected proposers
		log.Debug("---------------------------")
		log.Debug("result of elected proposers:")
		for idx, s := range proposers {
			log.Debug("proposer", "idx", idx, "addr", s.Hex())
		}
		log.Debug("current number", "number", s.number())
		log.Debug("future term(election term)", "term", term)
		log.Debug("---------------------------")
	}

	// Set default proposer if it is in initial stage
	if s.isUseDefaultProposers() {
		// set default proposers
		proposers := configs.Proposers()
		s.setRecentProposers(s.Term()+1, proposers)

		// some logs about default proposer in initialization state
		log.Debug("use default proposers for term", "term", s.Term()+1, "proposers", len(proposers))
		for i, p := range proposers {
			log.Debug(fmt.Sprintf("proposer #%d details", i), "address", p.Hex())
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

// ValidatorsOf returns validators of given block number
func (s *DporSnapshot) ValidatorsOf(number uint64) []common.Address {
	return s.getRecentValidators(s.TermOf(number))
}

// ProposersOf returns proposers of given block number
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
	proposers := s.ProposersOf(number)
	idx := int(((number - 1) % (s.config.TermLen * s.config.ViewLen)) / s.config.ViewLen)
	if idx >= 0 && idx < len(proposers) {
		if proposers[idx] == signer {
			return true, nil
		}
	}

	return false, errProposerNotInCommittee
}

// FutureValidatorsOf returns future validators of given block number
func (s *DporSnapshot) FutureValidatorsOf(number uint64) []common.Address {
	return s.getRecentValidators(s.FutureTermOf(number))
}

// FutureProposersOf returns future proposers of given block number
func (s *DporSnapshot) FutureProposersOf(number uint64) []common.Address {
	return s.getRecentProposers(s.FutureTermOf(number))
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

// StartBlockNumberOfTerm returns the first block number of a term
func (s *DporSnapshot) StartBlockNumberOfTerm(term uint64) uint64 {
	return s.config.ViewLen * s.config.TermLen * term
}

// choseDefaultProposers choses a batch of proposers from a proposers slice with total count of `defaultProposersNum`
// by the seed of current snapshot.hash.
func choseSomeProposers(allProposers []common.Address, seed int64, wantLen int) (defaultProposers []common.Address) {

	var proposers []common.Address
	for _, p := range allProposers {
		proposers = append(proposers, p)
	}

	if len(proposers) > wantLen {
		randSource := rand.NewSource(seed)
		myRand := rand.New(randSource)

		for i := 0; i < wantLen; i++ {
			chosen := myRand.Intn(len(proposers))
			defaultProposers = append(defaultProposers, proposers[chosen])
			proposers = append(proposers[:chosen], proposers[chosen+1:]...)
		}
		return defaultProposers
	} else if len(proposers) == wantLen {
		return proposers
	}
	panic("invalid length of given proposer list")
}

func evenlyInsertDefaultProposers(electedProposers []common.Address, chosenDefaultProposers []common.Address, seed int64, wantLen int) (proposers []common.Address) {

	// panic if length of slices is invalid
	if len(electedProposers)+len(chosenDefaultProposers) != wantLen {
		panic("invalid length when evenly inserting default proposers to elected proposers")
	}

	// generate a random generator
	randSource := rand.NewSource(seed)
	myRand := rand.New(randSource)

	slicesNum := len(chosenDefaultProposers)

	if wantLen%slicesNum != 0 {
		panic("invalid wanted length, not a multiple of 4")
	}

	step := wantLen / slicesNum

	for i := 0; i < slicesNum; i++ {
		var slice []common.Address

		// combine two sub slices
		slice = append(slice, electedProposers[i*(step-1):i*(step-1)+(step-1)]...)
		slice = append(slice, chosenDefaultProposers[i])

		// get random position of the chosen proposer
		pos := myRand.Intn(step)

		// swap
		tmp := slice[len(slice)-1]
		for j := step - 1; j > pos; j-- {
			slice[j] = slice[j-1]
		}
		slice[pos] = tmp

		// append to proposers
		proposers = append(proposers, slice...)
	}
	return
}
