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
	"bitbucket.org/cpchain/chain/accounts"
	"math/big"
	"reflect"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

type dporHelper interface {
	dporUtil
	verifyHeader(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header, verifySigs bool) error
	snapshot(d *Dpor, chain consensus.ChainReader, number uint64, hash common.Hash, parents []*types.Header) (*DporSnapshot, error)
	verifySeal(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
	verifySigs(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
	verifyProposers(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
	signHeader(d *Dpor, chain consensus.ChainReader, header *types.Header, state consensus.State) error
	validateBlock(d *Dpor, chain consensus.ChainReader, block *types.Block) error
}

type defaultDporHelper struct {
	dporUtil
}

// validateBlock checks basic fields in a block
func (dh *defaultDporHelper) validateBlock(c *Dpor, chain consensus.ChainReader, block *types.Block) error {
	// TODO: @AC consider if we need to verify body, as well as process txs and validate state
	return dh.verifyHeader(c, chain, block.Header(), nil, block.RefHeader(), false)
}

// verifyHeader checks whether a header conforms to the consensus rules.The
// caller may optionally pass in a batch of parents (ascending order) to avoid
// looking those up from the database. This is useful for concurrently verifying
// a batch of new headers.
func (dh *defaultDporHelper) verifyHeader(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header,
	refHeader *types.Header, verifySigs bool) error {
	if header.Number == nil {
		return errUnknownBlock
	}

	number := header.Number.Uint64()

	// Don't waste time checking blocks from the future
	if header.Time.Cmp(big.NewInt(time.Now().Unix())) > 0 {
		return consensus.ErrFutureBlock
	}

	switch d.fake {
	case DoNothingFakeMode:
		// do nothing
	case FakeMode:
		return nil
	}

	// Ensure the block's parent is valid
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
	if parent.Time.Uint64()+d.config.Period > header.Time.Uint64() {
		return ErrInvalidTimestamp
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
		if header.Difficulty == nil || header.Difficulty.Cmp(dporDifficulty) != 0 {
			return errInvalidDifficulty
		}
	}

	// verify proposers
	if err := d.dh.verifyProposers(d, chain, header, parents, refHeader); err != nil {
		log.Warn("verifying proposers failed", "error", err, "hash", header.Hash().Hex())
		return err
	}

	// verify dpor seal
	if err := dh.verifySeal(d, chain, header, parents, refHeader); err != nil {
		log.Warn("verifying seal failed", "error", err, "hash", header.Hash().Hex())
		return err
	}

	// verify dpor sigs if required
	if verifySigs {
		if err := dh.verifySigs(d, chain, header, parents, refHeader); err != nil {
			log.Warn("verifying validator signatures failed", "error", err, "hash", header.Hash().Hex())
			return err
		}
	}
	return nil
}

// verifyProposers verifies dpor proposers
func (dh *defaultDporHelper) verifyProposers(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error {
	// The genesis block is the always valid dead-end
	number := header.Number.Uint64()
	if number == 0 {
		return nil
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

	return nil
}

// verifValidators verifies dpor validators

// Snapshot retrieves the authorization Snapshot at a given point in time.
func (dh *defaultDporHelper) snapshot(dpor *Dpor, chain consensus.ChainReader, number uint64, hash common.Hash, parents []*types.Header) (*DporSnapshot, error) {
	// Search for a Snapshot in memory or on disk for checkpoints
	var (
		headers []*types.Header
		snap    *DporSnapshot
	)

	numberIter := number
	for snap == nil {
		// If an in-memory Snapshot was found, use that
		// TODO: @AC disable cache as the cache contains an invalid snapshot
		// if s, ok := dpor.recents.Get(hash); ok {
		// 	snap = s.(*DporSnapshot)
		// 	break
		// }

		// If an on-disk checkpoint Snapshot can be found, use that
		// if number%checkpointInterval == 0 {
		if IsCheckPoint(numberIter, dpor.config.TermLen, dpor.config.ViewLen) {
			if s, err := loadSnapshot(dpor.config, dpor.db, hash); err == nil {
				log.Debug("Loaded voting Snapshot from disk", "number", numberIter, "hash", hash)
				snap = s
				break
			}
		}

		// If we're at block zero, make a Snapshot
		if numberIter == 0 {
			// Retrieve genesis block and verify it
			genesis := chain.GetHeaderByNumber(0)
			if err := dpor.dh.verifyHeader(dpor, chain, genesis, nil, nil, false); err != nil {
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
			if header.Hash() != hash || header.Number.Uint64() != numberIter {
				log.Debug("consensus.ErrUnknownAncestor 1")
				return nil, consensus.ErrUnknownAncestor
			}
			parents = parents[:len(parents)-1]
		} else {
			// No explicit parents (or no more left), reach out to the database
			header = chain.GetHeader(hash, numberIter)
			if header == nil {
				log.Debug("consensus.ErrUnknownAncestor 2")
				return nil, consensus.ErrUnknownAncestor
			}
		}
		headers = append(headers, header)
		numberIter, hash = numberIter-1, header.ParentHash
	}

	// Previous Snapshot found, apply any pending headers on top of it
	for i := 0; i < len(headers)/2; i++ {
		headers[i], headers[len(headers)-1-i] = headers[len(headers)-1-i], headers[i]
	}

	dpor.lock.Lock()
	contractCaller := dpor.contractCaller
	dpor.lock.Unlock()

	// Apply headers to the snapshot and updates RPTs
	newSnap, err := snap.apply(headers, contractCaller)
	if err != nil {
		return nil, err
	}

	// Save to cache
	dpor.recents.Add(newSnap.hash(), newSnap)

	// If we've generated a new checkpoint Snapshot, save to disk
	if IsCheckPoint(newSnap.number(), dpor.config.TermLen, dpor.config.ViewLen) && len(headers) > 0 {
		if err = newSnap.store(dpor.db); err != nil {
			return nil, err
		}
		log.Debug("Stored voting Snapshot to disk", "number", newSnap.number(), "hash", newSnap.hash().Hex())
	}
	return newSnap, err
}

// verifySeal checks whether the dpor seal is signature of a correct proposer.
// The method accepts an optional list of parent headers that aren't yet part of the local blockchain to generate
// the snapshots from.
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

	// Resolve the authorization key and check against signers
	proposer, _, err := dh.ecrecover(header, dpor.signatures)
	if err != nil {
		return err
	}

	// Retrieve the Snapshot needed to verify this header and cache it
	snap, err := dh.snapshot(dpor, chain, number-1, header.ParentHash, parents[:len(parents)-1])
	if err != nil {
		return err
	}

	// Some debug infos here
	log.Debug("--------dpor.verifySeal--------")
	log.Debug("hash", "hash", hash.Hex())
	log.Debug("number", "number", number)
	log.Debug("current header", "number", chain.CurrentHeader().Number.Uint64())
	log.Debug("proposer", "address", proposer.Hex())

	// Check if the proposer is right proposer
	ok, err := snap.IsProposerOf(proposer, number)
	if err != nil {
		return err
	}
	// If proposer is a wrong leader, return err
	if !ok {
		return consensus.ErrUnauthorized
	}

	return nil
}

// verifySigs verifies whether the signatures of the header is signed by correct validator committee
func (dh *defaultDporHelper) verifySigs(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error {
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

	// Resolve the authorization keys
	proposer, validators, err := dh.ecrecover(header, dpor.signatures)
	if err != nil {
		return err
	}

	// Retrieve the Snapshot needed to verify this header and cache it

	snap, err := dh.snapshot(dpor, chain, number-1, header.ParentHash, parents[:len(parents)-1])
	if err != nil {
		return err
	}

	expectValidators := snap.ValidatorsOf(number)

	hash := header.Hash()
	// Some debug infos here
	log.Debug("--------dpor.verifySigs--------")
	log.Debug("hash", "hash", hash.Hex())
	log.Debug("number", "number", number)
	log.Debug("current header", "number", chain.CurrentHeader().Number.Uint64())
	log.Debug("proposer", "address", proposer.Hex())
	log.Debug("validators recovered from header: ")
	for idx, validator := range validators {
		log.Debug("validator", "addr", validator.Hex(), "idx", idx)
	}
	log.Debug("validators in snapshot: ")
	for idx, signer := range expectValidators {
		log.Debug("validator", "addr", signer.Hex(), "idx", idx)
	}

	if len(validators) != len(expectValidators) {
		return errInvalidValidatorSigs
	}

	count := 0
	for i, v := range validators {
		if v == expectValidators[i] {
			count++
		}
	}

	// if not reached to 2f + 1, the validation fails
	if count < (len(validators)-1)/3*2+1 {
		return errInvalidValidatorSigs
	}

	// pass
	return nil
}

// signHeader signs the given refHeader if self is in the committee
func (dh *defaultDporHelper) signHeader(dpor *Dpor, chain consensus.ChainReader, header *types.Header, state consensus.State) error {
	number := header.Number.Uint64()

	// Retrieve the Snapshot needed to verify this header and cache it
	snap, err := dh.snapshot(dpor, chain, number-1, header.ParentHash, nil)
	if err != nil {
		return err
	}

	// Sign the block if self is in the committee
	if snap.IsValidatorOf(dpor.signer, number) {
		// NOTE: sign a block only once
		if signedHash, signed := dpor.signedBlocks[header.Number.Uint64()]; signed && signedHash != header.Hash() {
			return errMultiBlocksInOneHeight
		}

		var bytesToHash []byte
		// Sign it
		if state == consensus.Preparing {
			bytesToHash = append([]byte{'P'}, dpor.dh.sigHash(header).Bytes()...) // Preparing block signed by 'P'+hash
		} else {
			bytesToHash = dpor.dh.sigHash(header).Bytes()
		}
		sighash, err := dpor.signFn(accounts.Account{Address: dpor.signer}, bytesToHash)
		if err != nil {
			return err
		}

		// Copy signer's signature to the right position in the allSigs
		sigPos, _ := snap.ValidatorViewOf(dpor.signer, number)
		copy(header.Dpor.Sigs[sigPos][:], sighash)

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
	ifStartDynamic := snap.isStartElection()

	return isCheckpoint && isFutureSigner && ifStartDynamic
}

func (dh *defaultDporHelper) uploadNodeInfo(dpor *Dpor, snap *DporSnapshot, number uint64) error {
	log.Info("In future committee, building the committee network...")

	term := snap.FutureTermOf(number)
	// TODO: @chengx add FutureValidatorsOf in snapshot.go
	signers := snap.FutureSignersOf(number)

	go func(eIdx uint64, committee []common.Address) {
		// Updates handler.signers
		err := dpor.validatorHandler.UpdateRemoteValidators(eIdx, committee)
		log.Debug("err when updating remote validators", "err", err)

		// Connect all
		err = dpor.validatorHandler.UploadEncryptedNodeInfo(eIdx)
		log.Debug("err when uploading my node info", "err", err)

	}(term, signers)

	return nil
}
