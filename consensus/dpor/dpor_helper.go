// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package dpor

import (
	"math/big"
	"reflect"
	"time"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

type dporHelper interface {
	dporUtil
	verifyHeader(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header, seal bool) error
	verifyCascadingFields(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header, seal bool) error
	snapshot(d *Dpor, chain consensus.ChainReader, number uint64, hash common.Hash, parents []*types.Header) (*DporSnapshot, error)
	verifySeal(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
	signHeader(d *Dpor, chain consensus.ChainReader, header *types.Header, state consensus.State) error
	validateBlock(d *Dpor, chain consensus.ChainReader, block *types.Block) error
}

type defaultDporHelper struct {
	dporUtil
}

// validateBlock checks basic fields in a block
func (dh *defaultDporHelper) validateBlock(c *Dpor, chain consensus.ChainReader, block *types.Block) error {
	return dh.verifyHeader(c, chain, block.Header(), nil, block.RefHeader(), false)
}

// verifyHeader checks whether a header conforms to the consensus rules.The
// caller may optionally pass in a batch of parents (ascending order) to avoid
// looking those up from the database. This is useful for concurrently verifying
// a batch of new headers.
func (dh *defaultDporHelper) verifyHeader(c *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header, seal bool) error {
	if header.Number == nil {
		return errUnknownBlock
	}

	number := header.Number.Uint64()

	// Don't waste time checking blocks from the future
	if header.Time.Cmp(big.NewInt(time.Now().Unix())) > 0 {
		return consensus.ErrFutureBlock
	}

	switch c.fake {
	case DoNothingFakeMode:
		// do nothing
	case FakeMode:
		return nil
	}

	// Check that the extra-data contains both the vanity and signature
	if len(header.Extra) < extraVanity {
		return errMissingVanity
	}

	// Ensure that the mix digest is zero as we don't have fork protection currently
	if header.MixHash != (common.Hash{}) {
		return errInvalidMixHash
	}

	// Ensure that the block's difficulty is meaningful (may not be correct at this point)
	if number > 0 {
		if header.Difficulty == nil || (header.Difficulty.Cmp(diffInTurn) != 0 && header.Difficulty.Cmp(diffNoTurn) != 0) {
			return errInvalidDifficulty
		}
	}

	// All basic checks passed, verify cascading fields
	return c.dh.verifyCascadingFields(c, chain, header, parents, refHeader, seal)
}

// verifyCascadingFields verifies all the header fields that are not standalone,
// rather depend on a batch of previous headers. The caller may optionally pass
// in a batch of parents (ascending order) to avoid looking those up from the
// database. This is useful for concurrently verifying a batch of new headers.
func (dh *defaultDporHelper) verifyCascadingFields(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header, seal bool) error {
	// The genesis block is the always valid dead-end
	number := header.Number.Uint64()
	if number == 0 {
		return nil
	}

	// Ensure that the block's timestamp isn't too close to it's parent
	var parent *types.Header
	if len(parents) > 0 {
		parent = parents[len(parents)-1]
	} else {
		// parent = chain.GetHeader(header.ParentHash, number-1)
		blk := chain.GetBlock(header.ParentHash, number-1)
		if blk != nil {
			parent = blk.Header()
		}
	}

	// Ensure that the block's parent is valid
	if parent == nil || parent.Number.Uint64() != number-1 || parent.Hash() != header.ParentHash {
		log.Debug("consensus.ErrUnknownAncestor 3")
		return consensus.ErrUnknownAncestor
	}

	// Ensure that the block's timestamp is valid
	if parent.Time.Uint64()+dpor.config.Period > header.Time.Uint64() {
		return ErrInvalidTimestamp
	}

	// Retrieve the Snapshot needed to verify this header and cache it
	snap, err := dh.snapshot(dpor, chain, number-1, header.ParentHash, parents)
	if err != nil {
		return err
	}

	// Check proposers
	proposers := make([]common.Address, dpor.config.TermLen)
	for pos, signer := range snap.ProposersOf(number) {
		proposers[pos] = signer
	}
	if !reflect.DeepEqual(header.Dpor.Proposers, proposers) {
		if NormalMode == dpor.fake {
			log.Debug("err: invalid proposer list")
			ps := snap.ProposersOf(number)

			log.Debug("~~~~~~~~~~~~~~~~~~~~~~~~")
			log.Debug("proposers in block dpor snap:")
			for round, signer := range ps {
				log.Debug("proposer", "addr", signer.Hex(), "idx", round)
			}

			log.Debug("~~~~~~~~~~~~~~~~~~~~~~~~")
			log.Debug("proposers in snapshot:")
			for round, signer := range snap.ValidatorsOf(number) {
				log.Debug("validator", "addr", signer.Hex(), "idx", round)
			}

			log.Debug("~~~~~~~~~~~~~~~~~~~~~~~~")
			log.Debug("recent proposers: ")
			for i := snap.TermOf(number); i < snap.TermOf(number)+5; i++ {
				log.Debug("----------------------")
				log.Debug("proposers in snapshot of:", "term idx", i)
				for _, s := range snap.getRecentProposers(i) {
					log.Debug("signer", "s", s.Hex())
				}
			}

			return errInvalidSigners
		}
	}

	// All basic checks passed, verify the seal and return
	if seal {
		return dh.verifySeal(dpor, chain, header, parents, refHeader)
	}

	return nil
}

// Snapshot retrieves the authorization Snapshot at a given point in time.
func (dh *defaultDporHelper) snapshot(dpor *Dpor, chain consensus.ChainReader, number uint64, hash common.Hash, parents []*types.Header) (*DporSnapshot, error) {
	// Search for a Snapshot in memory or on disk for checkpoints
	var (
		headers []*types.Header
		snap    *DporSnapshot
	)
	for snap == nil {
		// If an in-memory Snapshot was found, use that
		if s, ok := dpor.recents.Get(hash); ok {
			snap = s.(*DporSnapshot)
			break
		}

		// If an on-disk checkpoint Snapshot can be found, use that
		// if number%checkpointInterval == 0 {
		if IsCheckPoint(number, dpor.config.TermLen, dpor.config.ViewLen) {
			if s, err := loadSnapshot(dpor.config, dpor.db, hash); err == nil {
				log.Debug("Loaded voting Snapshot from disk", "number", number, "hash", hash)
				snap = s
				break
			}
		}

		// If we're at block zero, make a Snapshot
		if number == 0 {
			// Retrieve genesis block and verify it
			genesis := chain.GetHeaderByNumber(0)
			if err := dpor.dh.verifyHeader(dpor, chain, genesis, nil, nil, true); err != nil {
				return nil, err
			}

			var proposers []common.Address
			var validators []common.Address
			if dpor.fake == FakeMode || dpor.fake == DoNothingFakeMode {
				// do nothing when test,empty proposers assigned
			} else {
				// Create a snapshot from the genesis block
				proposers = genesis.Dpor.CopyProposers()
				validators = genesis.Dpor.CopyValidators()
			}
			snap = newSnapshot(dpor.config, 0, genesis.Hash(), proposers, validators)
			if err := snap.store(dpor.db); err != nil {
				return nil, err
			}
			log.Debug("Stored genesis voting Snapshot to disk")
			break
		}

		// No Snapshot for this header, gather the header and move backward
		var header *types.Header
		if len(parents) > 0 {
			// If we have explicit parents, pick from there (enforced)
			header = parents[len(parents)-1]
			if header.Hash() != hash || header.Number.Uint64() != number {
				log.Debug("consensus.ErrUnknownAncestor 1")
				return nil, consensus.ErrUnknownAncestor
			}
			parents = parents[:len(parents)-1]
		} else {
			// No explicit parents (or no more left), reach out to the database
			header = chain.GetHeader(hash, number)
			if header == nil {
				log.Debug("consensus.ErrUnknownAncestor 2")
				return nil, consensus.ErrUnknownAncestor
			}
		}
		headers = append(headers, header)
		number, hash = number-1, header.ParentHash
	}

	// Previous Snapshot found, apply any pending headers on top of it
	for i := 0; i < len(headers)/2; i++ {
		headers[i], headers[len(headers)-1-i] = headers[len(headers)-1-i], headers[i]
	}

	dpor.lock.Lock()
	contractCaller := dpor.contractCaller
	dpor.lock.Unlock()

	// Apply headers to the snapshot and updates RPTs
	snap, err := snap.apply(headers, contractCaller)
	if err != nil {
		return nil, err
	}

	// Save to cache
	dpor.recents.Add(snap.hash(), snap)

	// If we've generated a new checkpoint Snapshot, save to disk
	if IsCheckPoint(snap.number(), dpor.config.TermLen, dpor.config.ViewLen) && len(headers) > 0 {
		if err = snap.store(dpor.db); err != nil {
			return nil, err
		}
		log.Debug("Stored voting Snapshot to disk", "number", snap.number(), "hash", snap.hash())
	}
	return snap, err
}

// verifySeal checks whether the signature contained in the header satisfies the
// consensus protocol requirements. The method accepts an optional list of parent
// headers that aren't yet part of the local blockchain to generate the snapshots
// from.
func (dh *defaultDporHelper) verifySeal(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error {
	hash := header.Hash()
	number := header.Number.Uint64()

	// Verifying the genesis block is not supported
	if number == 0 {
		return errUnknownBlock
	}

	// Fake Dpor doesn't do seal check
	if dpor.fake == FakeMode || dpor.fake == DoNothingFakeMode {
		time.Sleep(dpor.fakeDelay)
		if dpor.fakeFail == number {
			return errFakerFail
		}
		return nil
	}

	inserted := chain.GetHeaderByHash(hash)
	// Already in chain
	if inserted != nil {
		return nil
	}

	// Resolve the authorization key and check against signers
	leader, signers, err := dpor.dh.ecrecover(header, dpor.signatures)
	if err != nil {
		return err
	}

	// Retrieve the Snapshot needed to verify this header and cache it
	snap, err := dh.snapshot(dpor, chain, number-1, header.ParentHash, parents)
	if err != nil {
		return err
	}

	// Some debug infos here
	log.Debug("--------dpor.verifySeal start--------")
	log.Debug("hash", "hash", hash.Hex())
	log.Debug("number", "number", number)
	log.Debug("current header", "number", chain.CurrentHeader().Number.Uint64())
	log.Debug("leader", "address", leader.Hex())
	log.Debug("signers recovered from header: ")
	for _, signer := range signers {
		log.Debug("signer", "address", signer.Hex())
	}
	log.Debug("signers in snapshot: ")
	for _, signer := range snap.ValidatorsOf(number) {
		log.Debug("signer", "address", signer.Hex())
	}

	// Check if the leader is the real leader
	ok, err := snap.IsProposerOf(leader, number)
	if err != nil {
		return err
	}
	// If leader is a wrong leader, return err
	if !ok {
		return consensus.ErrUnauthorized
	}

	// Check if accept the sigs and if leader is in the sigs
	accept, err := dpor.dh.acceptSigs(header, dpor.signatures, snap.ValidatorsOf(number), uint(dpor.config.TermLen))
	if err != nil {
		return err
	}

	// We haven't reached the 2/3 rule
	if !accept {
		return consensus.ErrNotEnoughSigs
	}

	return nil
}

// signHeader signs the given refHeader if self is in the committee
func (dh *defaultDporHelper) signHeader(dpor *Dpor, chain consensus.ChainReader, header *types.Header, state consensus.State) error {
	hash := header.Hash()
	number := header.Number.Uint64()

	// Retrieve the Snapshot needed to verify this header and cache it
	snap, err := dh.snapshot(dpor, chain, number-1, header.ParentHash, nil)
	if err != nil {
		return err
	}

	// Retrieve signatures of the block in cache
	s, ok := dpor.signatures.Get(hash)
	if !ok {
		s = &Signatures{
			sigs: make(map[common.Address][]byte),
		}
	}

	// Copy all signatures to allSigs
	allSigs := make([]types.DporSignature, dpor.config.TermLen)
	for signPos, signer := range snap.ValidatorsOf(number) {
		if sigHash, ok := s.(*Signatures).GetSig(signer); ok {
			copy(allSigs[signPos][:], sigHash)
		}
	}
	header.Dpor.Sigs = allSigs

	// Sign the block if self is in the committee
	if snap.IsValidatorOf(dpor.signer, number) {

		// NOTE: sign a block only once
		if signedHash, signed := dpor.signedBlocks[header.Number.Uint64()]; signed && signedHash != header.Hash() {
			return errMultiBlocksInOneHeight
		}

		// Sign it!
		sighash, err := dpor.signFn(accounts.Account{Address: dpor.signer}, dpor.dh.sigHash(header).Bytes())
		if err != nil {
			return err
		}

		// Copy signer's signature to the right position in the allSigs
		sigPos, _ := snap.ValidatorViewOf(dpor.signer, number)
		copy(allSigs[sigPos][:], sighash)
		header.Dpor.Sigs = allSigs

		return nil
	}
	return errValidatorNotInCommittee
}

// isTimeToDialValidators checks if it is time to dial remote signers, and dials them if time is up
func (dh *defaultDporHelper) isTimeToDialValidators(dpor *Dpor, chain consensus.ChainReader) bool {

	header := chain.CurrentHeader()
	number := header.Number.Uint64()

	// Retrieve the Snapshot needed to verify this header and cache it
	snap, err := dh.snapshot(dpor, chain, number, header.Hash(), nil)
	if err != nil {
		return false
	}

	// Some debug info
	log.Debug("my address", "eb", dpor.signer.Hex())
	log.Debug("current block number", "number", number)
	log.Debug("ISCheckPoint", "bool", IsCheckPoint(number, dpor.config.TermLen, dpor.config.ViewLen))
	log.Debug("is future signer", "bool", snap.IsFutureSignerOf(dpor.signer, number))
	log.Debug("term idx of block number", "block term index", snap.TermOf(number))

	log.Debug("recent signers: ")
	for i := snap.TermOf(number); i < snap.TermOf(number)+5; i++ {
		log.Debug("----------------------")
		log.Debug("signers in snapshot of:", "term idx", i)
		for _, s := range snap.getRecentSigners(i) {
			log.Debug("signer", "s", s.Hex())
		}
	}

	// If in a checkpoint and self is in the future committee, try to build the committee network
	isCheckpoint := IsCheckPoint(number, dpor.config.TermLen, dpor.config.ViewLen)
	isFutureSigner := snap.IsFutureSignerOf(dpor.signer, number)
	ifStartDynamic := number >= dpor.config.MaxInitBlockNumber

	return isCheckpoint && isFutureSigner && ifStartDynamic
}

func (dh *defaultDporHelper) dialValidators(dpor *Dpor, snap *DporSnapshot, number uint64) error {
	log.Info("In future committee, building the committee network...")

	term := snap.FutureTermOf(number)
	signers := snap.FutureSignersOf(number)

	go func(eIdx uint64, committee []common.Address) {
		// Updates handler.signers
		dpor.validatorHandler.UpdateSigners(eIdx, committee)
		// Connect all
		dpor.validatorHandler.DialAll()
	}(term, signers)

	return nil
}
