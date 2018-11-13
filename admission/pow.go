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

package admission

import (
	"time"

	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// pow base struct for pow.
type pow struct {
	// difficulty pow's difficulty.
	difficulty int64
	// address this node's address.
	address common.Address
	// header the header used for POW
	header *types.Header
	// lifeTime time limitation of pow.
	lifeTime time.Duration
	// nonce the number tries to find.
	nonce uint64
	// err unexpected err
	err error
}

// newPow returns struct pow.
func newPow(difficulty int64, lifeTime time.Duration, address common.Address, header *types.Header) *pow {
	return &pow{
		difficulty: difficulty,
		address:    address,
		header:     header,
		lifeTime:   lifeTime,
	}
}

func (p *pow) isOk() bool {
	return p.err == nil
}

func (p *pow) getError() error {
	return p.err
}
