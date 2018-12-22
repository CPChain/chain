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
	"math/big"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/rlp"
	lru "github.com/hashicorp/golang-lru"
)

func nanosecondToMillisecond(t int64) int64 {
	return t * int64(time.Nanosecond) / int64(time.Millisecond)
}

func millisecondToNanosecond(t int64) int64 {
	return t * int64(time.Millisecond) / int64(time.Nanosecond)
}

// Signatures stores sigs in a block
type Signatures struct {
	lock sync.RWMutex
	sigs map[common.Address][]byte
}

// GetSig gets addr's sig
func (s *Signatures) GetSig(addr common.Address) (sig []byte, ok bool) {
	s.lock.RLock()
	defer s.lock.RUnlock()
	sig, ok = s.sigs[addr]
	return sig, ok
}

// SetSig sets addr's sig
func (s *Signatures) SetSig(addr common.Address, sig []byte) {
	s.lock.Lock()
	defer s.lock.Unlock()
	s.sigs[addr] = sig
}

// IsCheckPoint returns if a given block number is in a checkpoint with given
// termLen and viewLen
func IsCheckPoint(number uint64, termLen uint64, viewLen uint64) bool {
	if number == 0 {
		return false
	}

	if termLen == 0 || viewLen == 0 {
		return true
	}
	return number%(termLen*viewLen) == 0
}

type dporUtil interface {
	sigHash(header *types.Header, salt []byte) (hash common.Hash)
	ecrecover(header *types.Header, sigcache *lru.ARCCache) (common.Address, []common.Address, error)
	acceptSigs(header *types.Header, sigcache *lru.ARCCache, signers []common.Address, termLen uint) (bool, error)
	percentagePBFT(n uint, N uint) bool
	calcDifficulty(snap *DporSnapshot, signer common.Address) *big.Int
}

type defaultDporUtil struct {
	lock sync.RWMutex
}

// sigHash returns the hash which is used as input for the proof-of-authority
// signing. It is the hash of the entire header apart from the 65 byte signature
// contained at the end of the extra data.
//
// Note, the method requires the extra data to be at least 65 bytes, otherwise it
// panics. This is done to avoid accidentally using both forms (signature present
// or not), which could be abused to produce different hashes for the same header.
func (d *defaultDporUtil) sigHash(header *types.Header, salt []byte) (hash common.Hash) {
	hasher := sha3.NewKeccak256()

	contentToHash := []interface{}{
		header.ParentHash,
		header.Coinbase,
		header.StateRoot,
		header.TxsRoot,
		header.ReceiptsRoot,
		header.LogsBloom,
		header.Difficulty,
		header.Number,
		header.GasLimit,
		header.GasUsed,
		header.Time,
		header.Dpor.Proposers,
		header.Dpor.Validators,
		header.Extra,
		common.Hash{},
		types.BlockNonce{},
	}
	if len(salt) > 0 { // if salt is empty, not append because even an empty slice will change hash, not meet the caller's intention.
		contentToHash = append(contentToHash, salt)
	}
	rlp.Encode(hasher, contentToHash)

	hasher.Sum(hash[:0])
	return hash
}

// ecrecover extracts the cpchain account address from a signed header.
// the return value is (the_proposer_address, validators_committee_addresses, error)
func (d *defaultDporUtil) ecrecover(header *types.Header, sigcache *lru.ARCCache) (common.Address, []common.Address, error) {
	d.lock.Lock()
	defer d.lock.Unlock()

	hash := header.Hash()

	if bytes.Equal(header.Dpor.Seal[:], new(types.DporSignature)[:]) {
		return common.Address{}, []common.Address{}, errMissingSignature
	}

	// Retrieve leader's signature
	proposerSig := header.Dpor.Seal

	// Recover the public key and the cpchain address of leader.
	var propser common.Address
	proposerPubKey, err := crypto.Ecrecover(d.sigHash(header, []byte{}).Bytes(), proposerSig[:])
	if err != nil {
		return common.Address{}, []common.Address{}, err
	}
	copy(propser[:], crypto.Keccak256(proposerPubKey[1:])[12:])

	// Cache proposer signature.
	if sigs, known := sigcache.Get(hash); known {
		sigs.(*Signatures).SetSig(propser, proposerSig[:])
	} else {
		sigs := &Signatures{
			sigs: make(map[common.Address][]byte),
		}
		sigs.SetSig(propser, proposerSig[:])
		sigcache.Add(hash, sigs)
	}

	// Recover the public key and the cpchain address of signers one by one.
	var validators []common.Address
	for i := 0; i < len(header.Dpor.Sigs); i++ {
		signerSig := header.Dpor.Sigs[i]

		noSigner := bytes.Equal(signerSig[:], make([]byte, extraSeal))
		if !noSigner {
			// Recover it!
			signerPubkey, err := crypto.Ecrecover(d.sigHash(header, []byte{}).Bytes(), signerSig[:])
			if err != nil {
				continue
			}

			var validator common.Address
			copy(validator[:], crypto.Keccak256(signerPubkey[1:])[12:])

			// Cache it!
			sigs, _ := sigcache.Get(hash)
			sigs.(*Signatures).SetSig(validator, signerSig[:])

			// Add signer to known signers
			validators = append(validators, validator)
		}
	}
	return propser, validators, nil
}

// acceptSigs checks that signatures have enough signatures to accept the block.
func (d *defaultDporUtil) acceptSigs(header *types.Header, sigcache *lru.ARCCache, signers []common.Address, termLen uint) (bool, error) {
	d.lock.Lock()
	defer d.lock.Unlock()

	numSigs := uint(0)
	hash := header.Hash()

	// Retrieve signatures of this header from cache
	if sigs, known := sigcache.Get(hash); known {
		for _, signer := range signers {
			if _, ok := sigs.(*Signatures).GetSig(signer); ok {
				numSigs++
			}
		}
	} else {
		return false, errNoSigsInCache
	}

	return numSigs >= (termLen-1)/3*2+1, nil
}

// percentagePBFT returns n is large than pctPBFT * N.
func (d *defaultDporUtil) percentagePBFT(n uint, N uint) bool {
	return uint(pctB)*n > uint(pctA)*N
}

// CalcDifficulty is the difficulty adjustment algorithm. It returns the difficulty
// that a new block should have based on the previous blocks in the chain and the
// current signer.
func (d *defaultDporUtil) calcDifficulty(snap *DporSnapshot, signer common.Address) *big.Int {
	return new(big.Int).Set(DporDifficulty)
}
