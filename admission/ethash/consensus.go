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

package ethash

import (
	"math/big"
	"runtime"

	"github.com/ethereum/go-ethereum/common"
)

// Verify implements consensus.Engine, checking whether the given block satisfies
// the PoW difficulty requirements.
func (ethash *Ethash) Verify(number, nonce uint64, signer common.Address) bool {
	header := ethash.chain.GetHeaderByNumber(number)
	cache := ethash.cache(number)
	size := datasetSize(number)
	_, result := hashimotoLight(size, cache.cache, header.HashNoNonce().Bytes(), nonce)
	// Caches are unmapped in a finalizer. Ensure that the cache stays live
	// until after the call to hashimotoLight so it's not unmapped while being used.
	runtime.KeepAlive(cache)

	target := new(big.Int).Div(maxUint256, new(big.Int).SetInt64(ethash.config.Difficulty))
	if new(big.Int).SetBytes(result).Cmp(target) > 0 {
		return false
	}
	return true
}
