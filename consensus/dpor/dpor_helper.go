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
	verifySeal(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
	verifySigs(d *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
	verifyProposers(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
	signHeader(d *Dpor, chain consensus.ChainReader, header *types.Header, state consensus.State) error
	validateBlock(d *Dpor, chain consensus.ChainReader, block *types.Block, verifySigs bool, verifyProposers bool) error
}

type defaultDporHelper struct {
	dporUtil
}

// validateBlock checks basic fields in a block
func (dh *defaultDporHelper) validateBlock(c *Dpor, chain consensus.ChainReader, block *types.Block, verifySigs bool, verifyProposers bool) error {
	// TODO: @AC consider if we need to verify body, as well as process txs and validate state
	return dh.verifyHeader(c, chain, block.Header(), nil, block.RefHeader(), verifySigs, verifyProposers)
}

// verifyHeader checks whether a header conforms to the consensus rules.The
// caller may optionally pass in a batch of parents (ascending order) to avoid
// looking those up from the database. This is useful for concurrently verifying
// a batch of new headers.
func (dh *defaultDporHelper) verifyHeader(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header,
	refHeader *types.Header, verifySigs bool, verifyProposers bool) error {
	if header.Number == nil {
		return errUnknownBlock
	}

	number := header.Number.Uint64()

	// Don't waste time checking blocks from the future
	if header.Time.Cmp(big.NewInt(nanosecondToMillisecond(time.Now().UnixNano()))) > 0 {
		return consensus.ErrFutureBlock
	}

	switch dpor.Mode() {
	case DoNothingFakeMode:
		// do nothing
	case FakeMode:
		return nil
	case PbftFakeMode:
		return nil
	}

	if header.Number.Uint64() > 0 {
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
		if parent == nil || parent.Number.Uint64() != number-1 || parent.Hash() != header.ParentHash {

			log.Debug("consensus.ErrUnknownAncestor 3")
			log.Debug("parent", "parent", parent)
			if parent != nil {
				log.Debug("parent.number", "number", parent.Number.Uint64(), "number-1", number-1)
				log.Debug("parent.hash", "hash", parent.Hash(), "header.ParentHash", header.ParentHash)
			}

			return consensus.ErrUnknownAncestor
		}

		// Ensure that the block's timestamp is valid
		if parent.Time.Uint64()+dpor.config.Period > header.Time.Uint64() {
			if dpor.Mode() == NormalMode {
				return ErrInvalidTimestamp
			}
		}
	}

	isImpeach := header.Coinbase == common.Address{}

	// Ensure that the block's difficulty is meaningful (may not be correct at this point)
	if number > 0 {
		if header.Difficulty == nil || (header.Difficulty.Cmp(DporDifficulty) != 0 && header.Difficulty.Uint64() != 0) {
			return errInvalidDifficulty
		}

		// verify dpor seal, genesis block not need this check
		if verifyProposers && !isImpeach { // ignore impeach block(whose coinbase is empty)
			if err := dh.verifySeal(dpor, chain, header, parents, refHeader); err != nil {
				log.Warn("verifying seal failed", "error", err, "hash", header.Hash().Hex())
				return err
			}
		}
	}

	if verifyProposers && !isImpeach {
		// verify proposers
		if err := dpor.dh.verifyProposers(dpor, chain, header, parents, refHeader); err != nil {
			log.Warn("verifying proposers failed", "error", err, "hash", header.Hash().Hex())
			return err
		}
	}

	// verify dpor sigs if required
	if number > 0 && verifySigs {
		if err := dh.verifySigs(dpor, chain, header, parents, refHeader); err != nil {
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
			//return nil
		}
	}

	return nil
}

// Snapshot retrieves the authorization Snapshot at a given point in time.
// @param chainSeg  the segment of a chain, composed by ancesters and the block(sepcified by parameter [number] and [hash])
// in the order of ascending block number.
func (dh *defaultDporHelper) snapshot(dpor *Dpor, chain consensus.ChainReader, number uint64, hash common.Hash, chainSeg []*types.Header) (*DporSnapshot, error) {
	// Search for a Snapshot in memory or on disk for checkpoints
	var (
		headers []*types.Header
		snap    *DporSnapshot
	)

	log.Debug("defaultDporHelper snapshot", "number", number, "hash", hash.Hex(), "len(parent and itself)", len(chainSeg))

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
				log.Info("unknown ancestor", "hash1", header.Hash().Hex(), "hash2", hash.Hex(), "number1", header.Number.Uint64(), "number2", numberIter)
				log.Debug("consensus.ErrUnknownAncestor 1")
				return nil, consensus.ErrUnknownAncestor
			}
			chainSeg = chainSeg[:len(chainSeg)-1]
		} else {
			// No explicit chainSeg (or no more left), reach out to the database
			header = chain.GetHeader(hash, numberIter)
			if header == nil {
				log.Debug("consensus.ErrUnknownAncestor 2", "number", numberIter)
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
		rptBackend, _ = rpt.NewRptService(client, dpor.config.Contracts[configs.ContractRpt])
	}

	// Set correct client and rptBackend
	snap.setClient(client)
	snap.rptBackend = rptBackend

	// Apply headers to the snapshot and updates RPTs
	newSnap, err := snap.apply(headers, client, dpor.IsMiner())
	if err != nil {
		return nil, err
	}

	// Save to cache
	// TODO: check if it needs a lock
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
	proposer, _, err := dh.ecrecover(header, dpor.finalSigs) // TODO: check if it needs a lock
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

// verifySigs verifies whether the signatures of the header is signed by correct validator committee
func (dh *defaultDporHelper) verifySigs(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error {
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
	if count < (len(validators)-1)/3*2+1 {
		return consensus.ErrNotEnoughSigs
	}

	if dpor.IsMiner() && dh.isTimeToDialValidators(dpor, dpor.chain) {
		err = dh.updateAndDial(dpor, snap, number)
		if err != nil {
			return err
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
	if state == consensus.Prepared || state == consensus.ImpeachPrepared {
		s, ok = dpor.finalSigs.Get(hash) // check if it needs a lock
		if !ok || s == nil {
			s = &Signatures{
				sigs: make(map[common.Address][]byte),
			}
			dpor.finalSigs.Add(hash, s)
		}
	} else if state == consensus.Preprepared || state == consensus.ImpeachPreprepared {
		s, ok = dpor.prepareSigs.Get(hash)
		if !ok || s == nil {
			s = &Signatures{
				sigs: make(map[common.Address][]byte),
			}
			dpor.prepareSigs.Add(hash, s)
		}
	} else {
		log.Warn("the state is unexpected for signing header", "state", state)
		return errInvalidStateForSign
	}

	// Copy all signatures to allSigs
	allSigs := make([]types.DporSignature, dpor.config.TermLen)
	validators := snap.ValidatorsOf(number)
	if dpor.config.TermLen != uint64(len(validators)) {
		log.Warn("validator committee length not equal to term length", "termLen", dpor.config.TermLen, "validatorLen", len(validators))
	}

	// fulfill all known validator signatures to dpor.sigs to accumulate
	for signPos, signer := range snap.ValidatorsOf(number) {
		if sigHash, ok := s.(*Signatures).GetSig(signer); ok {
			copy(allSigs[signPos][:], sigHash)
		}
	}
	header.Dpor.Sigs = allSigs

	// Sign the block if self is in the committee
	if snap.IsValidatorOf(dpor.Coinbase(), number) {
		// NOTE: sign a block only once
		if signedHash, signed := dpor.IfSigned(number); signed && signedHash != header.Hash() {
			return errMultiBlocksInOneHeight
		}

		var hashToSign []byte
		// Sign it
		if state == consensus.Preprepared {
			// hashToSign = dpor.dh.sigHash(header, []byte{'P'}).Bytes() // Preparing block signed by 'P'+hash
			hashToSign = dpor.dh.sigHash(header, []byte{}).Bytes()
		} else {
			hashToSign = dpor.dh.sigHash(header, []byte{}).Bytes()
		}
		sighash, err := dpor.SignHash(hashToSign)
		if err != nil {
			log.Warn("signing block header failed", "error", err)
			return err
		}

		// if the sigs length is wrong, reset it with correct length(termLen)
		if len(header.Dpor.Sigs) != int(snap.config.TermLen) {
			header.Dpor.Sigs = make([]types.DporSignature, snap.config.TermLen)
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
		s.(*Signatures).SetSig(dpor.Coinbase(), sighash)

		return nil
	}
	log.Warn("signing block failed", "error", errValidatorNotInCommittee)
	return errValidatorNotInCommittee
}

// isTimeToDialValidators checks if it is time to dial remote signers, and dials them if time is up
func (dh *defaultDporHelper) isTimeToDialValidators(dpor *Dpor, chain consensus.ChainReader) bool {
	header := chain.CurrentHeader()
	number := header.Number.Uint64()
	snap := dpor.CurrentSnap()

	isStartElec := snap.isStartElection()
	if !isStartElec {
		return false
	}

	// Some debug info
	log.Debug("my address", "eb", dpor.Coinbase().Hex())
	log.Debug("current block number", "number", number)
	log.Debug("ISCheckPoint", "bool", IsCheckPoint(number, dpor.config.TermLen, dpor.config.ViewLen))
	log.Debug("is future signer", "bool", snap.IsFutureSignerOf(dpor.Coinbase(), number))
	log.Debug("term idx of block number", "block term index", snap.TermOf(number))

	log.Debug("recent proposers: ")
	for i := snap.TermOf(number); i < snap.TermOf(number)+5; i++ {
		log.Debug("----------------------")
		log.Debug("proposers in snapshot of:", "term idx", i)
		for _, p := range snap.getRecentProposers(i) {
			log.Debug("proposer", "s", p.Hex())
		}
		log.Debug("validators in snapshot of:", "term idx", i)
		for _, v := range snap.getRecentValidators(i) {
			log.Debug("validator", "s", v.Hex())
		}
		log.Debug("----------------------")
	}

	// If in a checkpoint and self is in the future committee, try to build the committee network
	isCheckpoint := IsCheckPoint(number, dpor.config.TermLen, dpor.config.ViewLen)
	isFutureSigner := snap.IsFutureProposerOf(dpor.Coinbase(), number)

	return isCheckpoint && isFutureSigner
}

func (dh *defaultDporHelper) updateAndDial(dpor *Dpor, snap *DporSnapshot, number uint64) error {
	log.Info("In future committee, building the committee network...")

	term := snap.FutureTermOf(number)

	// TODO: I need FutureValidatorsOf
	validators := snap.FutureSignersOf(number)

	go func(term uint64, remoteValidators []common.Address) {

		// Updates RemoteValidators in handler
		err := dpor.handler.UpdateRemoteValidators(term, remoteValidators)
		if err != nil {
			log.Warn("err when updating remote validators", "err", err)
		}

		// Dial all remote validators
		err = dpor.handler.DialAllRemoteValidators(term)
		if err != nil {
			log.Warn("err when dialing remote validators", "err", err)
		}

	}(term, validators)

	return nil
}
