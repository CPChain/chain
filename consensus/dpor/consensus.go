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
	"bytes"
	"context"
	"errors"
	"math/big"
	"time"

	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"bitbucket.org/cpchain/chain/core/state"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// Dpor proof-of-reputation protocol constants.
const (
	termLen       = uint(4)    // Default number of proposers.
	viewLen       = uint(4)    // Default number of blocks one signer can generate in one committee.
	campaignTerms = uint64(10) // Default number of terms to campaign for proposer committee.

	extraVanity = 32 // Fixed number of extra-data prefix bytes reserved for signer vanity
	extraSeal   = 65 // Fixed number of extra-data suffix bytes reserved for signer seal
)

var (
	DporDifficulty = big.NewInt(1) // Block difficulty for out-of-turn signatures
)

// Various error messages to mark blocks invalid. These should be private to
// prevent engine specific errors from being referenced in the remainder of the
// codebase, inherently breaking if the engine is swapped out. Please put common
// error types into the consensus package.
var (
	// errUnknownBlock is returned when the list of signers is requested for a block
	// that is not part of the local blockchain.
	errUnknownBlock = errors.New("unknown block")

	// errInvalidCheckpointBeneficiary is returned if a checkpoint/epoch transition
	// block has a beneficiary set to non-zeroes.
	errInvalidCheckpointBeneficiary = errors.New("beneficiary in checkpoint block non-zero")

	// errMissingVanity is returned if a block's extra-data section is shorter than
	// 32 bytes, which is required to store the signer vanity.
	errMissingVanity = errors.New("extra-data 32 byte vanity prefix missing")

	// errMissingSignature is returned if a block's extra-data section doesn't seem
	// to contain a 65 byte secp256k1 signature.
	errMissingSignature = errors.New("extra-data 65 byte suffix signature missing")

	// errInvalidDifficulty is returned if the difficulty of a block is not either
	// of 1 or 2, or if the value does not match the turn of the signer.
	errInvalidDifficulty = errors.New("invalid difficulty")

	// ErrInvalidTimestamp is returned if the timestamp of a block is lower than
	// the previous block's timestamp + the minimum block period.
	ErrInvalidTimestamp = errors.New("invalid timestamp")

	// errInvalidChain is returned if an authorization list is attempted to
	// be modified via out-of-range or non-contiguous headers.
	errInvalidChain = errors.New("invalid voting chain")

	// --- new error types ---

	// errMultiBlocksInOneHeight is returned if there is multi blocks in one height in the chain.
	errMultiBlocksInOneHeight = errors.New("multi blocks in one height")

	// errInvalidValidatorSigs is returned if the dpor sigs are not sigend by correct validator committtee.
	errInvalidValidatorSigs = errors.New("invalid validator signatures")

	// errNoSigsInCache is returned if the cache is unable to store and return sigs.
	errNoSigsInCache = errors.New("signatures not found in cache")

	errFakerFail = errors.New("error fake fail")

	// --- our new error types ---

	// errVerifyUncleNotAllowed is returned when verify uncle block.
	errVerifyUncleNotAllowed = errors.New("uncles not allowed")

	// errWaitTransactions is returned if an empty block is attempted to be sealed
	// on an instant chain (0 second period). It's important to refuse these as the
	// block reward is zero, so an empty block just bloats the chain... fast.
	errWaitTransactions = errors.New("waiting for transactions")

	errInvalidStateForSign = errors.New("the state is unexpected for signing header")
)

// Author implements consensus.Engine, returning the cpchain address recovered
// from the signature in the header's extra-data section.
func (d *Dpor) Author(header *types.Header) (common.Address, error) {
	proposer, _, err := d.dh.ecrecover(header, d.finalSigs)
	return proposer, err
}

// VerifyHeader checks whether a header conforms to the consensus rules.
func (d *Dpor) VerifyHeader(chain consensus.ChainReader, header *types.Header, verifySigs bool, refHeader *types.Header) error {
	return d.dh.verifyHeader(d, chain, header, nil, refHeader, verifySigs, false)
}

// VerifyHeaders is similar to VerifyHeader, but verifies a batch of headers. The
// method returns a quit channel to abort the operations and a results channel to
// retrieve the async verifications (the order is that of the input slice).
func (d *Dpor) VerifyHeaders(chain consensus.ChainReader, headers []*types.Header, verifySigs []bool, refHeaders []*types.Header) (chan<- struct{}, <-chan error) {
	abort := make(chan struct{})
	results := make(chan error, len(headers))

	go func() {
		for i, header := range headers {
			err := d.dh.verifyHeader(d, chain, header, headers[:i], refHeaders[i], verifySigs[i], false)

			select {
			case <-abort:
				return
			case results <- err:
			}
		}
	}()
	return abort, results
}

// VerifySeal implements consensus.Engine, checking whether the signature contained
// in the header satisfies the consensus protocol requirements.
func (d *Dpor) VerifySeal(chain consensus.ChainReader, header *types.Header, refHeader *types.Header) error {
	return d.dh.verifySeal(d, chain, header, nil, refHeader)
}

// VerifySigs checks if header has enough signatures of validators.
func (d *Dpor) VerifySigs(chain consensus.ChainReader, header *types.Header, refHeader *types.Header) error {
	return d.dh.verifySigs(d, chain, header, nil, refHeader)
}

// PrepareBlock implements consensus.Engine, preparing all the consensus fields of the
// header for running the transactions on top.
func (d *Dpor) PrepareBlock(chain consensus.ChainReader, header *types.Header) error {
	number := header.Number.Uint64()

	snap := d.CurrentSnap()
	if snap != nil {
		log.Debug("check if participate campaign", "isToCampaign", d.IsToCampaign(), "isStartCampaign", snap.isStartCampaign(), "number", snap.number())
		if d.IsToCampaign() && snap.isStartCampaign() {
			newTerm := d.CurrentSnap().TermOf(number)
			if newTerm > d.lastCampaignTerm+campaignTerms-1 {
				d.lastCampaignTerm = newTerm
				log.Info("campaign for proposer committee", "eleTerm", newTerm)
				d.client.Campaign(context.Background(), campaignTerms)
			}
		}
	}

	// Create a snapshot
	snap, err := d.dh.snapshot(d, chain, number-1, header.ParentHash, nil)
	if err != nil {
		return err
	}

	// Set the correct difficulty
	header.Difficulty = d.dh.calcDifficulty(snap, d.Coinbase())

	// Ensure the extra data has all its components
	if len(header.Extra) < extraVanity {
		header.Extra = append(header.Extra, bytes.Repeat([]byte{0x00}, extraVanity-len(header.Extra))...)
	}
	header.Extra = header.Extra[:extraVanity]

	for _, proposer := range snap.ProposersOf(number) {
		header.Dpor.Proposers = append(header.Dpor.Proposers, proposer)
	}

	log.Debug("prepare a block", "number", header.Number.Uint64(), "proposers", header.Dpor.ProposersFormatText(),
		"validators", header.Dpor.ValidatorsFormatText())

	// Set correct signatures size
	header.Dpor.Sigs = make([]types.DporSignature, d.config.ValidatorsLen)

	// Ensure the timestamp has the correct delay
	parent := chain.GetHeader(header.ParentHash, number-1)
	if parent == nil {
		log.Warn("consensus.ErrUnknownAncestor 4", "number", number, "parentHash", header.ParentHash.Hex())
		return consensus.ErrUnknownAncestor
	}
	header.Time = new(big.Int).Add(parent.Time, new(big.Int).SetUint64(d.config.Period))
	if header.Time.Int64() < nanosecondToMillisecond(time.Now().UnixNano()) {
		header.Time = big.NewInt(nanosecondToMillisecond(time.Now().UnixNano()))
	}
	return nil
}

func addCoinbaseReward(coinbase common.Address, state *state.StateDB) {
	amount := new(big.Int).Set(configs.Cep1BlockReward)
	state.AddBalance(coinbase, amount)
}

// Finalize implements consensus.Engine, ensuring no uncles are set, nor block
// rewards given, and returns the final block.
func (d *Dpor) Finalize(chain consensus.ChainReader, header *types.Header, state *state.StateDB, txs []*types.Transaction, uncles []*types.Header, receipts []*types.Receipt) (*types.Block, error) {
	addCoinbaseReward(header.Coinbase, state)
	// last step
	header.StateRoot = state.IntermediateRoot(true)
	// Assemble and return the final block for sealing
	return types.NewBlock(header, txs, receipts), nil
}

// Authorize injects a private key into the consensus engine to mint new blocks
// with.
func (d *Dpor) Authorize(signer common.Address, signFn backend.SignFn) {
	d.coinbaseLock.Lock()
	d.coinbase = signer
	d.signFn = signFn
	d.coinbaseLock.Unlock()

	if d.handler == nil {
		d.handler = backend.NewHandler(d.config, d.Coinbase())
	}
	if d.handler.Coinbase() != signer {
		d.handler.SetCoinbase(signer)
	}
}

// Seal implements consensus.Engine, attempting to create a sealed block using
// the local signing credentials.
// NB please populate the correct field values.  we are now removing some fields such as nonce.
func (d *Dpor) Seal(chain consensus.ChainReader, block *types.Block, stop <-chan struct{}) (*types.Block, error) {
	var (
		header = block.Header()
		number = header.Number.Uint64()

		coinbase = d.Coinbase()
		signFn   = d.SignHash
	)

	// Sealing the genesis block is not supported
	if number == 0 {
		return nil, errUnknownBlock
	}

	// For 0-period chains, refuse to seal empty blocks (no reward but would spin sealing)
	if d.config.Period == 0 && len(block.Transactions()) == 0 {
		return nil, errWaitTransactions
	}

	// Don't hold the signer fields for the entire sealing procedure

	// Bail out if we're unauthorized to sign a block
	snap, err := d.dh.snapshot(d, chain, number-1, header.ParentHash, nil)
	if err != nil {
		return nil, err
	}

	ok, err := snap.IsProposerOf(coinbase, number)
	if err != nil {
		if err == errProposerNotInCommittee {
			return nil, consensus.ErrNotInProposerCommittee
		} else {
			log.Debug("Error occurs when seal block", "error", err)
			return nil, err
		}
	}
	if !ok {
		return nil, consensus.ErrUnauthorized
	}

	// Sweet, the protocol permits us to sign the block, wait for our time
	delay := time.Duration(millisecondToNanosecond((header.Time.Int64() - nanosecondToMillisecond(time.Now().UnixNano()))))
	log.Debug("Waiting for slot to sign and propagate", "delay", common.PrettyDuration(delay))

	select {
	case <-stop:
		return nil, nil
	case <-time.After(delay):
		log.Debug("wait for seal", "delay", delay)
	}

	// Proposer seals the block with signature
	sighash, err := signFn(d.dh.sigHash(header).Bytes())
	if err != nil {
		return nil, err
	}
	copy(header.Dpor.Seal[:], sighash)

	// Create a signature space for validators
	header.Dpor.Sigs = make([]types.DporSignature, len(header.Dpor.Validators))
	log.Info("sealed the block", "hash", header.Hash().Hex(), "number", header.Number)

	// Update dpor current snapshot
	d.SetCurrentSnap(snap)

	return block.WithSeal(header), nil
}

// CalcDifficulty is the difficulty adjustment algorithm. It returns the difficulty
// that a new block should have based on the previous blocks in the chain and the
// current signer.
func (d *Dpor) CalcDifficulty(chain consensus.ChainReader, time uint64, parent *types.Header) *big.Int {
	snap, err := d.dh.snapshot(d, chain, parent.Number.Uint64(), parent.Hash(), nil)
	if err != nil {
		return nil
	}
	return d.dh.calcDifficulty(snap, d.Coinbase())
}

// APIs implements consensus.Engine, returning the user facing RPC API to allow
// controlling the signer voting.
func (d *Dpor) APIs(chain consensus.ChainReader) []rpc.API {
	return []rpc.API{{
		Namespace: "dpor",
		Version:   "1.0",
		Service:   &API{chain: chain, dpor: d},
		Public:    false,
	}}
}

// State returns current pbft phrase, one of (PrePrepare, Prepare, Commit).
func (d *Dpor) State() consensus.State {
	d.stateLock.Lock()
	defer d.stateLock.Unlock()
	return d.pbftState
}

// GetCalcRptInfo get the rpt value of an address at specific block number
func (d *Dpor) GetCalcRptInfo(address common.Address, blockNum uint64) int64 {
	instance, err := rpt.NewRptService(d.Client(), d.config.Contracts[configs.ContractRpt])
	if err != nil {
		log.Fatal("GetCalcRptInfo", "error", err)
	}
	rp := instance.CalcRptInfo(address, blockNum)
	return rp.Rpt
}
