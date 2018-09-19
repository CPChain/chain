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

// Package dpor implements the dpor consensus engine.
package dpor

import (
	"bytes"
	"math/big"
	"strconv"
	"time"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/misc"
	"bitbucket.org/cpchain/chain/core/types"
	"bitbucket.org/cpchain/chain/log"
)

type dporHelper interface {
	dporUtil
	verifyHeader(c *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
	verifyCascadingFields(c *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
	snapshot(c *Dpor, chain consensus.ChainReader, number uint64, hash common.Hash, parents []*types.Header) (*DporSnapshot, error)
	verifySeal(c *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error
}

type defaultDporHelper struct {
	dporUtil
}

// verifyHeader checks whether a header conforms to the consensus rules.The
// caller may optionally pass in a batch of parents (ascending order) to avoid
// looking those up from the database. This is useful for concurrently verifying
// a batch of new headers.
func (dh *defaultDporHelper) verifyHeader(c *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error {
	if header.Number == nil {
		return errUnknownBlock
	}
	number := header.Number.Uint64()

	// Don't waste time checking blocks from the future
	if header.Time.Cmp(big.NewInt(time.Now().Unix())) > 0 {
		return consensus.ErrFutureBlock
	}

	// Checkpoint blocks need to enforce zero beneficiary
	checkpoint := (number % c.config.Epoch) == 0
	if checkpoint && header.Coinbase != (common.Address{}) {
		return errInvalidCheckpointBeneficiary
	}

	// Check that the extra-data contains both the vanity and signature
	if len(header.Extra) < extraVanity {
		return errMissingVanity
	}
	if len(header.Extra) < extraVanity+extraSeal {
		return errMissingSignature
	}

	// Ensure that the extra-data contains a signer list on checkpoint, but none otherwise
	signersBytes := len(header.Extra) - extraVanity - extraSeal
	if signersBytes%common.AddressLength != 0 {
		return errInvalidSigners
	}

	// Ensure that the mix digest is zero as we don't have fork protection currently
	if header.MixDigest != (common.Hash{}) {
		return errInvalidMixDigest
	}

	// Ensure that the block doesn't contain any uncles which are meaningless in PoA
	if header.UncleHash != uncleHash {
		return errInvalidUncleHash
	}

	// Ensure that the block's difficulty is meaningful (may not be correct at this point)
	if number > 0 {
		if header.Difficulty == nil || (header.Difficulty.Cmp(diffInTurn) != 0 && header.Difficulty.Cmp(diffNoTurn) != 0) {
			return errInvalidDifficulty
		}
	}

	// If all checks passed, validate any special fields for hard forks
	if err := misc.VerifyForkHashes(chain.Config(), header, false); err != nil {
		return err
	}

	// All basic checks passed, verify cascading fields
	return c.dh.verifyCascadingFields(c, chain, header, parents, refHeader)
}

// verifyCascadingFields verifies all the header fields that are not standalone,
// rather depend on a batch of previous headers. The caller may optionally pass
// in a batch of parents (ascending order) to avoid looking those up from the
// database. This is useful for concurrently verifying a batch of new headers.
func (dh *defaultDporHelper) verifyCascadingFields(dpor *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error {
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
		parent = chain.GetHeader(header.ParentHash, number-1)
	}
	if parent == nil || parent.Number.Uint64() != number-1 || parent.Hash() != header.ParentHash {
		return consensus.ErrUnknownAncestor
	}
	if parent.Time.Uint64()+dpor.config.Period > header.Time.Uint64() {
		return ErrInvalidTimestamp
	}
	// Retrieve the Snapshot needed to verify this header and cache it
	snap, err := dh.snapshot(dpor, chain, number-1, header.ParentHash, parents)
	if err != nil {
		return err
	}
	// Check signers bytes in extraData
	signers := make([]byte, dpor.config.Epoch*common.AddressLength)
	for round, signer := range snap.signers() {
		copy(signers[round*common.AddressLength:(round+1)*common.AddressLength], signer[:])
	}
	extraSuffix := len(header.Extra) - extraSeal
	if !bytes.Equal(header.Extra[extraVanity:extraSuffix], signers) {
		return errInvalidSigners
	}
	// All basic checks passed, verify the seal and return
	return dh.verifySeal(dpor, chain, header, parents, refHeader)
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
		if number%checkpointInterval == 0 {
			if s, err := loadSnapshot(dpor.config, dpor.signatures, dpor.db, hash); err == nil {
				log.Trace("Loaded voting Snapshot from disk", "number", number, "hash", hash)
				snap = s
				break
			}
		}
		// If we're at block zero, make a Snapshot
		if number == 0 {
			genesis := chain.GetHeaderByNumber(0)
			if err := dpor.dh.verifyHeader(dpor, chain, genesis, nil, nil); err != nil {
				return nil, err
			}
			signers := make([]common.Address, (len(genesis.Extra)-extraVanity-extraSeal)/common.AddressLength)
			for i := 0; i < len(signers); i++ {
				copy(signers[i][:], genesis.Extra[extraVanity+i*common.AddressLength:])
			}
			snap = newSnapshot(dpor.config, dpor.signatures, 0, genesis.Hash(), signers)
			if err := snap.store(dpor.db); err != nil {
				return nil, err
			}
			log.Trace("Stored genesis voting Snapshot to disk")
			break
		}
		// No Snapshot for this header, gather the header and move backward
		var header *types.Header
		if len(parents) > 0 {
			// If we have explicit parents, pick from there (enforced)
			header = parents[len(parents)-1]
			if header.Hash() != hash || header.Number.Uint64() != number {
				return nil, consensus.ErrUnknownAncestor
			}
			parents = parents[:len(parents)-1]
		} else {
			// No explicit parents (or no more left), reach out to the database
			header = chain.GetHeader(hash, number)
			if header == nil {
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
	snap, err := snap.apply(headers)
	if err != nil {
		return nil, err
	}
	dpor.recents.Add(snap.Hash, snap)

	// If we've generated a new checkpoint Snapshot, save to disk
	if snap.Number%checkpointInterval == 0 && len(headers) > 0 {
		if err = snap.store(dpor.db); err != nil {
			return nil, err
		}
		log.Trace("Stored voting Snapshot to disk", "number", snap.Number, "hash", snap.Hash)
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

	// Retrieve the Snapshot needed to verify this header and cache it
	snap, err := dh.snapshot(dpor, chain, number-1, header.ParentHash, parents)
	if err != nil {
		return err
	}

	// Resolve the authorization key and check against signers
	leader, signers, err := dpor.dh.ecrecover(header, dpor.signatures)
	if err != nil {
		return err
	}

	// --- our check starts ---
	// Some debug infos here.
	log.Debug("--------I am in dpor.verifySeal start--------")
	log.Debug("hash: " + hash.Hex())
	log.Debug("number: " + strconv.Itoa(int(number)))
	log.Debug("current header: " + strconv.Itoa(int(chain.CurrentHeader().Number.Uint64())))
	log.Debug("leader: " + leader.Hex())
	log.Debug("signers: ")
	for round, signer := range signers {
		log.Debug(strconv.Itoa(round) + ": " + signer.Hex())
	}
	log.Debug("--------I am in dpor.verifySeal end--------")

	// Check if the leader is the real leader.
	ok, err := snap.isLeader(leader, number)
	if err != nil {
		return err
	}
	if !ok {
		return consensus.ErrUnauthorized
	}

	// Check if accept the sigs and if leader is in the sigs.
	accept, err := dpor.dh.acceptSigs(header, dpor.signatures, snap.signers())
	if err != nil {
		return err
	}

	s, _ := dpor.signatures.Get(hash)
	sigs := s.(map[common.Address][]byte)

	// Copy all signatures recovered to allSigs.
	allSigs := make([]byte, int(dpor.config.Epoch)*extraSeal)
	for round, signer := range snap.signers() {
		if sigHash, ok := sigs[signer]; ok {
			copy(allSigs[round*extraSeal:(round+1)*extraSeal], sigHash)
		}
	}

	// Encode allSigs to header.extra2.
	err = refHeader.EncodeToExtra2(types.Extra2Struct{Type: types.TypeExtra2Signatures, Data: allSigs})
	if err != nil {
		return err
	}

	// We haven't reached the 2/3 rule.
	if !accept {
		// Sign the block if self is in the committee.
		if snap.isSigner(dpor.signer) {
			// NOTE: only sign a block once.
			if signedHash, signed := dpor.signedBlocks[header.Number.Uint64()]; signed && signedHash != header.Hash() {
				return errMultiBlocksInOneHeight
			}
			// Sign it!
			sighash, err := dpor.signFn(accounts.Account{Address: dpor.signer}, dpor.dh.sigHash(header).Bytes())
			if err != nil {
				return err
			}
			round, _ := snap.signerRound(dpor.signer)

			// Copy signer's signature to the right position in the allSigs.
			copy(allSigs[round*extraSeal:(round+1)*extraSeal], sighash)

			// Encode to header.extra2
			err = refHeader.EncodeToExtra2(types.Extra2Struct{Type: types.TypeExtra2Signatures, Data: allSigs})
			if err != nil {
				return err
			}

		} else {
			return consensus.ErrNotEnoughSigs
		}
	}
	// --- our check ends ---

	// Ensure that the difficulty corresponds to the turn-ness of the signer
	inturn, _ := snap.isLeader(leader, header.Number.Uint64())
	if inturn && header.Difficulty.Cmp(diffInTurn) != 0 {
		return errInvalidDifficulty
	}
	if !inturn && header.Difficulty.Cmp(diffNoTurn) != 0 {
		return errInvalidDifficulty
	}
	return nil
}
