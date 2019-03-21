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
	"reflect"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

type dporHelper interface {
	dporUtil

	verifyHeader(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header,
		verifySigs bool, verifyProposers bool) error

	snapshot(d *Dpor, chain consensus.ChainReader, number uint64, hash common.Hash, parents []*types.Header) (*DporSnapshot, error)

	verifyBasic(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
	verifySeal(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
	verifySignatures(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
	verifyProposers(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error

	signHeader(d *Dpor, chain consensus.ChainReader, header *types.Header, state consensus.State) error
	validateBlock(d *Dpor, chain consensus.ChainReader, block *types.Block, verifySigs bool, verifyProposers bool) error
}

type defaultDporHelper struct {
	dporUtil
}

// validateBlock checks basic fields in a block
func (dh *defaultDporHelper) validateBlock(c *Dpor, chain consensus.ChainReader, block *types.Block, verifySigs bool, verifyProposers bool) error {
	return dh.verifyHeader(c, chain, block.Header(), nil, block.RefHeader(), verifySigs, verifyProposers)
}

// verifyHeader checks whether a header conforms to the consensus rules.The
// caller may optionally pass in a batch of parents (ascending order) to avoid
// looking those up from the database. This is useful for concurrently verifying
// a batch of new headers.
func (dh *defaultDporHelper) verifyHeader(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header,
	refHeader *types.Header, verifySigs bool, verifyProposers bool) error {

	var (
		number    = header.Number.Uint64()
		isImpeach = header.Coinbase == common.Address{}
	)

	// verify basic fields of the header
	err := dh.verifyBasic(dpor, chain, header, parents, refHeader)
	if err != nil {
		return err
	}

	if number == 0 {
		return nil
	}

	// verify dpor seal, genesis block not need this check
	if verifyProposers && !isImpeach { // ignore impeach block(whose coinbase is empty)

		// verify proposers if it is not an impeachment block
		if err := dpor.dh.verifyProposers(dpor, chain, header, parents, refHeader); err != nil {
			log.Warn("verifying proposers failed", "error", err, "hash", header.Hash().Hex())
			return err
		}

		// verify proposer's seal
		if err := dh.verifySeal(dpor, chain, header, parents, refHeader); err != nil {
			log.Warn("verifying seal failed", "error", err, "hash", header.Hash().Hex())
			return err
		}
	}

	// verify dpor signatures if required
	if verifySigs {
		if err := dh.verifySignatures(dpor, chain, header, parents, refHeader); err != nil {
			log.Warn("verifying validator signatures failed", "error", err, "hash", header.Hash().Hex())
			return err
		}
	}

	return nil
}

// verifyBasic verifies basic fields of the header, i.e. Number, Hash, Coinbase, Time
func (dh *defaultDporHelper) verifyBasic(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error {

	// if nil number, return error
	if header.Number == nil {
		return errUnknownBlock
	}

	// switch dpor mode, test related
	switch dpor.Mode() {
	case DoNothingFakeMode:
		// do nothing
	case FakeMode:
		return nil
	case PbftFakeMode:
		return nil
	}

	var (
		number    = header.Number.Uint64()
		hash      = header.Hash()
		isImpeach = header.Coinbase == common.Address{}
	)

	if number == 0 {
		return nil
	}

	// Ensure the block's parent is valid
	var parent *types.Header
	if len(parents) > 0 {
		parent = parents[len(parents)-1]
	} else {
		blk := chain.GetBlock(header.ParentHash, number-1)
		if blk != nil {
			parent = blk.Header()
		}
	}

	// Ensure that the block's parent is valid
	if parent == nil {
		log.Debug("parent is nil when verifying the header", "number", number, "hash", hash)
		return consensus.ErrUnknownAncestor
	}
	if parent.Number.Uint64() != number-1 {
		log.Debug("parent's number is not equal to header.number when verifying the header", "number", number, "hash", hash, "parent.number", parent.Number.Uint64())
		return consensus.ErrUnknownAncestor
	}
	if parent.Hash() != header.ParentHash {
		log.Debug("parent's hash is not equal to header.parentHash when verifying the header", "number", number, "hash", hash, "parent.hash", parent.Hash().Hex(), "header.parentHash", header.ParentHash.Hex())
		return consensus.ErrUnknownAncestor
	}

	// If timestamp is in a valid field, wait for it, otherwise, return invalid timestamp.
	log.Debug("timestamp related values", "parent timestamp", parent.Timestamp(), "block timestamp", header.Timestamp(), "period", dpor.config.PeriodDuration(), "timeout", dpor.config.ImpeachTimeout)

	// Ensure that the block's timestamp is valid
	if dpor.Mode() == NormalMode && number > dpor.config.MaxInitBlockNumber && !isImpeach {

		if header.Timestamp().Before(parent.Timestamp().Add(dpor.config.PeriodDuration())) {
			return ErrInvalidTimestamp
		}
		if header.Timestamp().After(parent.Timestamp().Add(dpor.config.PeriodDuration()).Add(dpor.config.ImpeachTimeout)) {
			return ErrInvalidTimestamp
		}
	}

	// Delay to verify it!
	delay := header.Timestamp().Sub(time.Now())
	log.Debug("delaying to verify the block", "delay", delay)
	<-time.After(delay)

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
	proposers := snap.ProposersOf(number)
	if !reflect.DeepEqual(header.Dpor.Proposers, proposers) {
		if dpor.Mode() == NormalMode {
			log.Debug("err: invalid proposer list")
			log.Debug("~~~~~~~~~~~~~~~~~~~~~~~~")
			log.Debug("proposers in block dpor snap:")
			for round, signer := range header.Dpor.Proposers {
				log.Debug("proposer", "addr", signer.Hex(), "idx", round)
			}

			log.Debug("~~~~~~~~~~~~~~~~~~~~~~~~")
			log.Debug("proposers in snapshot:")
			for round, signer := range proposers {
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

			return consensus.ErrInvalidSigners
		}
	}

	return nil
}

// Snapshot retrieves the authorization Snapshot at a given point in time.
// @param chainSeg  the segment of a chain, composed by ancestors and the block(specified by parameter [number] and [hash])
// in the order of ascending block number.
func (dh *defaultDporHelper) snapshot(dpor *Dpor, chain consensus.ChainReader, number uint64, hash common.Hash, chainSeg []*types.Header) (*DporSnapshot, error) {
	// Search for a Snapshot in memory or on disk for checkpoints
	var (
		headers []*types.Header
		snap    *DporSnapshot
	)

	log.Debug("defaultDporHelper snapshot", "number", number, "hash", hash.Hex(), "len(parent and itself)", len(chainSeg))

	// return early if already know it!
	if dpor.CurrentSnap() != nil && dpor.CurrentSnap().hash() == hash {
		return dpor.CurrentSnap(), nil
	}

	numberIter := number
	for snap == nil {

		// If an in-memory snapshot can be found, use it
		if got, ok := dpor.recentSnaps.Get(hash); ok {
			snap = got.(*DporSnapshot)
			break
		}

		// If an on-disk checkpoint Snapshot can be found, use that
		if IsCheckPoint(numberIter, dpor.config.TermLen, dpor.config.ViewLen) {
			log.Debug("loading snapshot", "number", numberIter, "hash", hash)
			s, err := loadSnapshot(dpor.config, dpor.db, hash)
			if err == nil {
				log.Debug("Loaded checkpoint Snapshot from disk", "number", numberIter, "hash", hash)
				snap = s
				break
			} else if numberIter != number {
				log.Debug("loading snapshot fails", "error", err)
			}
		}

		// If we're at block zero, make a Snapshot
		if numberIter == 0 {
			// Retrieve genesis block and verify it
			genesis := chain.GetHeaderByNumber(0)
			if err := dpor.dh.verifyHeader(dpor, chain, genesis, nil, nil, false, false); err != nil {
				return nil, err
			}

			var proposers []common.Address
			var validators []common.Address
			if dpor.Mode() == FakeMode || dpor.Mode() == DoNothingFakeMode {
				// do nothing when test,empty proposers assigned
			} else {
				// Create a snapshot from the genesis block
				proposers = genesis.Dpor.CopyProposers()
				validators = genesis.Dpor.CopyValidators()
			}
			snap = newSnapshot(dpor.config, 0, genesis.Hash(), proposers, validators, FakeMode)
			if err := snap.store(dpor.db); err != nil {
				return nil, err
			}
			log.Debug("Stored genesis voting Snapshot to disk")
			break
		}

		// No Snapshot for this header, gather the header and move backward
		var header *types.Header
		if len(chainSeg) > 0 {
			// If we have explicit chainSeg, pick from there (enforced)
			header = chainSeg[len(chainSeg)-1]
			if header.Hash() != hash || header.Number.Uint64() != numberIter {
				return nil, consensus.ErrUnknownAncestor
			}
			chainSeg = chainSeg[:len(chainSeg)-1]
		} else {
			// No explicit chainSeg (or no more left), reach out to the database
			header = chain.GetHeader(hash, numberIter)
			if header == nil {
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

	var (
		client     = snap.client()
		rptBackend = snap.rptBackend
	)

	if client == nil {
		client = dpor.Client()
	}

	if rptBackend == nil && client != nil {
		if dpor.rptBackend == nil {
			rptBackend, err := rpt.NewRptService(client, dpor.config.Contracts[configs.ContractRpt])
			if err != nil {
				log.Debug("err when create new rpt service", "err", err)
			}
			dpor.rptBackend = rptBackend

			log.Debug("created new rpt service")
		}

		rptBackend = dpor.rptBackend
	}

	// Set correct client and rptBackend
	snap.setClient(client)
	snap.rptBackend = rptBackend

	// Apply headers to the snapshot and updates RPTs
	newSnap, err := snap.apply(headers, client, dpor.IsMiner() || dpor.IsValidator())
	if err != nil {
		return nil, err
	}

	// Save to cache
	dpor.recentSnaps.Add(newSnap.hash(), newSnap)

	// If we've generated a new checkpoint Snapshot, save to disk
	if IsCheckPoint(newSnap.number(), dpor.config.TermLen, dpor.config.ViewLen) && len(headers) > 0 {
		if err = newSnap.store(dpor.db); err != nil {
			log.Warn("failed to store dpor snapshot", "error", err)
			return nil, err
		}
		log.Debug("Stored voting Snapshot to disk", "number", newSnap.number(), "hash", newSnap.hash().Hex())
	}

	dpor.SetCurrentSnap(newSnap)

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
	if dpor.Mode() == FakeMode || dpor.Mode() == DoNothingFakeMode {
		time.Sleep(dpor.fakeDelay)
		if dpor.fakeFail == number {
			return errFakerFail
		}
		return nil
	}

	// Resolve the authorization key and check against signers
	proposer, _, err := dh.ecrecover(header, dpor.finalSigs)
	if err != nil {
		return err
	}

	// Retrieve the Snapshot needed to verify this header and cache it
	snap, err := dh.snapshot(dpor, chain, number-1, header.ParentHash, parents)
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

// verifySignatures verifies whether the signatures of the header is signed by correct validator committee
func (dh *defaultDporHelper) verifySignatures(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error {
	var (
		number    = header.Number.Uint64()
		hash      = header.Hash()
		isImpeach = header.Coinbase == common.Address{}
	)

	// Verifying the genesis block is not supported
	if number == 0 {
		return errUnknownBlock
	}

	// Fake Dpor doesn't do seal check
	if dpor.Mode() == FakeMode || dpor.Mode() == DoNothingFakeMode {
		time.Sleep(dpor.fakeDelay)
		if dpor.fakeFail == number {
			return errFakerFail
		}
		return nil
	}

	// Resolve the authorization keys
	proposer, validators, err := dh.ecrecover(header, dpor.finalSigs)
	if err != nil {
		return err
	}

	// Retrieve the Snapshot needed to verify this header and cache it
	snap, err := dh.snapshot(dpor, chain, number-1, header.ParentHash, parents)
	if err != nil {
		return err
	}

	expectValidators := snap.ValidatorsOf(number)

	// Some debug infos here
	log.Debug("--------dpor.verifySigs--------")
	log.Debug("hash", "hash", hash.Hex())
	log.Debug("number", "number", number)
	log.Debug("current header", "number", chain.CurrentHeader().Number.Uint64())
	log.Debug("proposer", "address", proposer.Hex())

	defaultValidators, _ := dpor.ValidatorsOf(chain.CurrentHeader().Number.Uint64())
	log.Debug("number of validators", "count", len(defaultValidators))

	log.Debug("validators recovered from header: ")
	for idx, validator := range validators {
		log.Debug("validator", "addr", validator.Hex(), "idx", idx)
	}
	log.Debug("validators in snapshot: ")
	for idx, signer := range expectValidators {
		log.Debug("validator", "addr", signer.Hex(), "idx", idx)
	}

	count := 0
	for _, v := range validators {
		for _, ev := range expectValidators {
			if v == ev {
				count++
			}
		}
	}

	// if not reached to 2f + 1, the validation fails
	if !isImpeach {
		if !dpor.config.Certificate(uint64(count)) {
			return consensus.ErrNotEnoughSigs
		}
	} else {
		if !dpor.config.ImpeachCertificate(uint64(count)) {
			return consensus.ErrNotEnoughSigs
		}
	}

	// pass
	return nil
}

// signHeader signs the given refHeader if self is in the committee
func (dh *defaultDporHelper) signHeader(dpor *Dpor, chain consensus.ChainReader, header *types.Header, state consensus.State) error {
	hash := header.Hash()
	number := header.Number.Uint64()

	// Retrieve the Snapshot needed to verify this header and cache it
	snap, err := dh.snapshot(dpor, chain, number-1, header.ParentHash, nil)
	if err != nil {
		log.Warn("getting dpor snapshot failed", "error", err)
		return err
	}

	var s interface{}
	var ok bool
	// Retrieve signatures of the block in cache
	if state == consensus.Commit || state == consensus.ImpeachCommit {
		s, ok = dpor.finalSigs.Get(hash) // check if it needs a lock
		if !ok || s == nil {
			s = &signatures{
				sigs: make(map[common.Address][]byte),
			}
			dpor.finalSigs.Add(hash, s)
		}
	} else if state == consensus.Prepare || state == consensus.ImpeachPrepare {
		s, ok = dpor.prepareSigs.Get(hash)
		if !ok || s == nil {
			s = &signatures{
				sigs: make(map[common.Address][]byte),
			}
			dpor.prepareSigs.Add(hash, s)
		}
	} else {
		log.Warn("the state is unexpected for signing header", "state", state)
		return errInvalidStateForSign
	}

	// Copy all signatures to allSigs
	allSigs := make([]types.DporSignature, dpor.config.ValidatorsLen())
	validators := snap.ValidatorsOf(number)
	if dpor.config.ValidatorsLen() != uint64(len(validators)) {
		log.Warn("validator committee length not equal to validators length", "config.ValidatorsLen", dpor.config.ValidatorsLen(), "validatorLen", len(validators))
	}

	// fulfill all known validator signatures to dpor.sigs to accumulate
	for signPos, signer := range snap.ValidatorsOf(number) {
		if sigHash, ok := s.(*signatures).getSig(signer); ok {
			copy(allSigs[signPos][:], sigHash)
		}
	}
	header.Dpor.Sigs = allSigs

	// Sign the block if self is in the committee
	if snap.IsValidatorOf(dpor.Coinbase(), number) {
		// NOTE: sign a block only once
		if signedHash, signed := dpor.IfSigned(number); signed && signedHash != header.Hash() && state != consensus.ImpeachPrepare && state != consensus.ImpeachCommit {
			return errMultiBlocksInOneHeight
		}

		// get hash with state
		hashToSign, err := hashBytesWithState(dpor.dh.sigHash(header).Bytes(), state)
		if err != nil {
			log.Warn("failed to get hash bytes with state", "number", number, "hash", hash.Hex(), "state", state)
			return err
		}

		// Sign it
		sighash, err := dpor.SignHash(hashToSign)
		if err != nil {
			log.Warn("signing block header failed", "error", err)
			return err
		}

		// if the sigs length is wrong, reset it with correct ValidatorsLen
		if len(header.Dpor.Sigs) != int(snap.config.ValidatorsLen()) {
			header.Dpor.Sigs = make([]types.DporSignature, snap.config.ValidatorsLen())
		}

		// mark as signed
		err = dpor.MarkAsSigned(number, hash)
		if err != nil {
			return err
		}

		// Copy signer's signature to the right position in the allSigs
		sigPos, _ := snap.ValidatorViewOf(dpor.Coinbase(), number)
		copy(header.Dpor.Sigs[sigPos][:], sighash)

		// Record new sig to signature cache
		s.(*signatures).setSig(dpor.Coinbase(), sighash)

		return nil
	}
	log.Warn("signing block failed", "error", errValidatorNotInCommittee)
	return errValidatorNotInCommittee
}
