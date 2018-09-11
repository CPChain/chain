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

	"fmt"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/hashicorp/golang-lru"
)

type dporUtil interface {
	sigHash(header *types.Header) (hash common.Hash)
	ecrecover(header *types.Header, sigcache *lru.ARCCache) (common.Address, []common.Address, error)
	acceptSigs(header *types.Header, sigcache *lru.ARCCache, signers []common.Address) (bool, error)
	percentagePBFT(n uint, N uint) bool
	calcDifficulty(snap *DporSnapshot, signer common.Address) *big.Int
}

type defaultDporUtil struct {
}

// sigHash returns the hash which is used as input for the proof-of-authority
// signing. It is the hash of the entire header apart from the 65 byte signature
// contained at the end of the extra data.
//
// Note, the method requires the extra data to be at least 65 bytes, otherwise it
// panics. This is done to avoid accidentally using both forms (signature present
// or not), which could be abused to produce different hashes for the same header.
func (d *defaultDporUtil) sigHash(header *types.Header) (hash common.Hash) {
	hasher := sha3.NewKeccak256()

	rlp.Encode(hasher, []interface{}{
		header.ParentHash,
		header.UncleHash,
		header.Coinbase,
		header.Root,
		header.TxHash,
		header.ReceiptHash,
		header.Bloom,
		header.Difficulty,
		header.Number,
		header.GasLimit,
		header.GasUsed,
		header.Time,
		header.Extra[:len(header.Extra)-65],
		header.MixDigest,
		header.Nonce,
	})
	hasher.Sum(hash[:0])
	return hash
}

// ecrecover extracts the Ethereum account address from a signed header.
// the return value is (leader_address, signer_addresses, error)
func (d *defaultDporUtil) ecrecover(header *types.Header, sigcache *lru.ARCCache) (common.Address, []common.Address, error) {

	hash := header.Hash()

	if len(header.Extra) < extraSeal {
		return common.Address{}, []common.Address{}, errMissingSignature
	}

	// NOTE: Header extraData field format:
	// header.Extra[extraVanity:Committee:leader-sig]
	// header.Extra2[signer1-sig:...:signerN-sig]

	leaderSig := header.Extra[len(header.Extra)-extraSeal:]
	// signersSig := header.Extra2[:]
	ss, err := header.DecodedExtra2(types.TypeExtra2SignaturesDecoder)
	if err != nil {
		return common.Address{}, []common.Address{}, err
	}
	signersSig := ss.Data

	// Recover the public key and the Ethereum address of leader.
	leaderPubkey, err := crypto.Ecrecover(d.sigHash(header).Bytes(), leaderSig)
	if err != nil {
		return common.Address{}, []common.Address{}, err
	}
	var leader common.Address
	copy(leader[:], crypto.Keccak256(leaderPubkey[1:])[12:])

	fmt.Println("hash hex:", hash.Hex())
	// Cache leader signature.
	if sigs, known := sigcache.Get(hash); known {
		sigs.(map[common.Address][]byte)[leader] = leaderSig
	} else {
		sigs := make(map[common.Address][]byte)
		sigs[leader] = leaderSig
		sigcache.Add(hash, sigs)
	}

	// Return if there is no signers' signatures.
	if len(signersSig)%extraSeal != 0 {
		return leader, []common.Address{}, errInvalidSigBytes
	}

	var signers []common.Address
	for i := 0; i < len(signersSig)/extraSeal; i++ {
		// Recover the public key and the Ethereum address of signers one by one.
		signerSig := signersSig[i*extraSeal : (i+1)*extraSeal]

		noSigner := bytes.Equal(signerSig, make([]byte, extraSeal))
		if !noSigner {
			// Recover it!
			signerPubkey, err := crypto.Ecrecover(d.sigHash(header).Bytes(), signerSig)
			if err != nil {
				return common.Address{}, signers, err
			}
			var signer common.Address
			copy(signer[:], crypto.Keccak256(signerPubkey[1:])[12:])

			//fmt.Println("signer hex:", signer.Hex())
			//fmt.Println("signerSig hex:", common.Bytes2Hex(signerSig))
			// Cache it!
			sigs, _ := sigcache.Get(hash)
			sigs.(map[common.Address][]byte)[signer] = signerSig

			signers = append(signers, signer)
		}
	}
	return leader, signers, nil
}

// acceptSigs checks that signatures have enough signatures to accept the block.
func (d *defaultDporUtil) acceptSigs(header *types.Header, sigcache *lru.ARCCache, signers []common.Address) (bool, error) {
	numSigs := uint(0)
	accept := false
	hash := header.Hash()

	if sigs, known := sigcache.Get(hash); known {
		s := sigs.(map[common.Address][]byte)
		for _, signer := range signers {
			if _, ok := s[signer]; ok {
				numSigs++
			}
		}
	} else {
		return false, errNotSigsInCache
	}

	// num of sigs must > 2/3 * epochLength, leader must be in the sigs.
	if d.percentagePBFT(numSigs, epochLength) {
		accept = true
	}
	return accept, nil
}

// percentagePBFT returns n is large than pctPBFT * N.
func (d *defaultDporUtil) percentagePBFT(n uint, N uint) bool {
	return uint(pctB)*n > uint(pctA)*N
}

// CalcDifficulty is the difficulty adjustment algorithm. It returns the difficulty
// that a new block should have based on the previous blocks in the chain and the
// current signer.
func (d *defaultDporUtil) calcDifficulty(snap *DporSnapshot, signer common.Address) *big.Int {
	if ok, _ := snap.isLeader(signer, snap.Number+1); ok {
		return new(big.Int).Set(diffInTurn)
	}
	return new(big.Int).Set(diffNoTurn)
}
