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
	"errors"
	"math/big"
	"time"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/api/grpc"
	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/core/state"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// Dpor proof-of-reputation protocol constants.
const (
	termLen = uint(4) // Default number of signers.
	viewLen = uint(4) // Default number of blocks one signer can generate in one committee.

	// blockPeriod = uint(1) // Default minimum difference between two consecutive block's timestamps

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

	// errInvalidMixHash is returned if a block's mix digest is non-zero.
	errInvalidMixHash = errors.New("non-zero mix digest")

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

	// errInvalidSigners is returned if a block contains an invalid extra sigers bytes.
	errInvalidSigners = errors.New("invalid signer list on checkpoint block")

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
)

// SignFn is a signer callback function to request a hash to be signed by a
// backing account.
type SignFn func(accounts.Account, []byte) ([]byte, error)

// Author implements consensus.Engine, returning the cpchain address recovered
// from the signature in the header's extra-data section.
func (d *Dpor) Author(header *types.Header) (common.Address, error) {
	proposer, _, err := d.dh.ecrecover(header, d.signatures)
	return proposer, err
}

// VerifyHeader checks whether a header conforms to the consensus rules.
func (d *Dpor) VerifyHeader(chain consensus.ChainReader, header *types.Header, verifySigs bool, refHeader *types.Header) error {
	return d.dh.verifyHeader(d, chain, header, nil, refHeader, verifySigs)
}

// VerifyHeaders is similar to VerifyHeader, but verifies a batch of headers. The
// method returns a quit channel to abort the operations and a results channel to
// retrieve the async verifications (the order is that of the input slice).
func (d *Dpor) VerifyHeaders(chain consensus.ChainReader, headers []*types.Header, verifySigs []bool, refHeaders []*types.Header) (chan<- struct{}, <-chan error) {
	abort := make(chan struct{})
	results := make(chan error, len(headers))

	go func() {
		for i, header := range headers {
			err := d.dh.verifyHeader(d, chain, header, headers[:i], refHeaders[i], verifySigs[i])

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

func (d *Dpor) VerifySigs(chain consensus.ChainReader, header *types.Header, refHeader *types.Header) error {
	return d.dh.verifySigs(d, chain, header, nil, refHeader)
}

// PrepareBlock implements consensus.Engine, preparing all the consensus fields of the
// header for running the transactions on top.
func (d *Dpor) PrepareBlock(chain consensus.ChainReader, header *types.Header) error {
	// If the block isn't a checkpoint, cast a random vote (good enough for now)
	header.Coinbase = common.Address{}
	header.Nonce = types.BlockNonce{}

	number := header.Number.Uint64()

	// Assemble the voting Snapshot to check which votes make sense
	snap, err := d.dh.snapshot(d, chain, number-1, header.ParentHash, nil)
	if err != nil {
		return err
	}

	// Set the correct difficulty
	header.Difficulty = d.dh.calcDifficulty(snap, d.proposer)

	// Ensure the extra data has all its components
	if len(header.Extra) < extraVanity {
		header.Extra = append(header.Extra, bytes.Repeat([]byte{0x00}, extraVanity-len(header.Extra))...)
	}
	header.Extra = header.Extra[:extraVanity]

	// TODO differentiate signer from validator/proposer
	for _, signer := range snap.ProposersOf(number) {
		header.Dpor.Proposers = append(header.Dpor.Proposers, signer)
	}

	// TODO WRONG this should be validator set size
	header.Dpor.Sigs = make([]types.DporSignature, d.config.TermLen)
	// Mix digest is reserved for now, set to empty
	header.MixHash = common.Hash{}

	// Ensure the timestamp has the correct delay
	parent := chain.GetHeader(header.ParentHash, number-1)
	if parent == nil {
		log.Debug("consensus.ErrUnknownAncestor 4")
		return consensus.ErrUnknownAncestor
	}
	header.Time = new(big.Int).Add(parent.Time, new(big.Int).SetUint64(d.config.Period))
	if header.Time.Int64() < time.Now().Unix() {
		header.Time = big.NewInt(time.Now().Unix())
	}
	return nil
}

func addCoinbaseReward(coinbase common.Address, state *state.StateDB) {
	amount := big.NewInt(configs.Cep1BlockReward)
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
func (d *Dpor) Authorize(signer common.Address, signFn SignFn) {
	d.lock.Lock()
	defer d.lock.Unlock()

	d.signer = signer
	d.signFn = signFn

	if d.validatorHandler == nil {
		d.validatorHandler = backend.NewHandler(d.config, d.Signer())
	}
	if d.validatorHandler.Coinbase() != signer {
		d.validatorHandler.SetCoinbase(signer)
	}
}

// Seal implements consensus.Engine, attempting to create a sealed block using
// the local signing credentials.
func (d *Dpor) Seal(chain consensus.ChainReader, block *types.Block, stop <-chan struct{}) (*types.Block, error) {
	header := block.Header()

	// Sealing the genesis block is not supported
	number := header.Number.Uint64()
	if number == 0 {
		return nil, errUnknownBlock
	}
	// For 0-period chains, refuse to seal empty blocks (no reward but would spin sealing)
	if d.config.Period == 0 && len(block.Transactions()) == 0 {
		return nil, errWaitTransactions
	}
	// Don't hold the signer fields for the entire sealing procedure
	d.lock.RLock()
	signer, signFn := d.signer, d.signFn
	d.lock.RUnlock()

	// Bail out if we're unauthorized to sign a block
	snap, err := d.dh.snapshot(d, chain, number-1, header.ParentHash, nil)
	if err != nil {
		return nil, err
	}

	ok, err := snap.IsProposerOf(d.signer, number)
	if err != nil {
		log.Warn("Error occurs when seal block", "error", err)
		return nil, err
	}
	if !ok {
		return nil, consensus.ErrUnauthorized
	}

	/*
		// TODO: fix this logic.
		// Sweet, the protocol permits us to sign the block, wait for our time
		delay := time.Unix(header.Time.Int64(), 0).Sub(time.Now()) // nolint: gosimple
		if header.Difficulty.Cmp(diffNoTurn) == 0 {
			// It's not our turn explicitly to sign, delay it a bit
			wiggle := time.Duration(len(snap.Signers)/2+1) * wiggleTime
			delay += time.Duration(rand.Int63n(int64(wiggle)))

			log.Debug("Out-of-turn signing requested", "wiggle", common.PrettyDuration(wiggle))
		}
		log.Debug("Waiting for slot to sign and propagate", "delay", common.PrettyDuration(delay))

		select {
		case <-stop:
			return nil, nil
		case <-time.After(delay):
		}
	*/
	// Proposer seals the block with signature
	sighash, err := signFn(accounts.Account{Address: signer}, d.dh.sigHash(header).Bytes())
	if err != nil {
		return nil, err
	}
	copy(header.Dpor.Seal[:], sighash)

	// Create a signature space for validators
	header.Dpor.Sigs = make([]types.DporSignature, len(header.Dpor.Validators))
	log.Info("sealed the block", "hash", header.Hash().Hex(), "number", header.Number)

	d.currentSnapshot = snap

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
	return d.dh.calcDifficulty(snap, d.signer)
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

// GAPIs is APIs for dpor.
func (d *Dpor) GAPIs(chain consensus.ChainReader) []grpc.GApi {
	return []grpc.GApi{}
}

// IsFutureSigner implements Validator.
// TODO: @shiyc remove it later
func (d *Dpor) IsFutureSigner(chain consensus.ChainReader, address common.Address, number uint64) (bool, error) {
	d.lock.Lock()
	defer d.lock.Unlock()

	return true, nil

	// TODO
	// snap, err := d.dh.snapshot(d, chain, number-1, chain.GetHeaderByNumber(number).ParentHash, nil)
	// if err != nil {
	// 	return false, err
	// }

	// if snap.ifUseDefaultSigners() {
	// 	for _, signer := range snap.candidates() {
	// 		if signer == address {
	// 			return true, nil
	// 		}
	// 	}
	// 	return false, nil
	// }
	// log.Debug("checking signers...")

	// return snap.IsFutureSignerOf(address, number) || snap.IsSignerOf(address, number), nil
}

//IsFutureValidator implements proposer
func (d *Dpor) IsFutureProposer(chain consensus.ChainReader, address common.Address, number uint64) (bool, error) {
	d.lock.Lock()
	defer d.lock.Unlock()
	return true, nil
	//TODO: @shiyc implement it
}

// State returns current pbft phrase, one of (PrePrepare, Prepare, Commit).
func (d *Dpor) State() consensus.State {
	d.lock.Lock()
	defer d.lock.Unlock()
	return d.pbftState
}
