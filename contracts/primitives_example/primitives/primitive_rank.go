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

package primitives

import (
	"math/big"

	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/ethereum/go-ethereum/common"
)

//go:generate abigen --sol ../contracts/primitive_contracts.sol --pkg contracts --out ../contracts/primitive_contracts.go

// Definitions of primitive contracts

type GetRank struct {
	Backend RptPrimitiveBackend
}

func (c *GetRank) RequiredGas(input []byte) uint64 {
	return configs.GetRankGas
}

func (c *GetRank) Run(input []byte) ([]byte, error) {
	addr, number, err := extractRptPrimitivesArgs(input)
	if err != nil {
		log.Error("primitive_rank got error", "error", err)
		return common.LeftPadBytes(new(big.Int).Bytes(), 32), nil
	}
	log.Debug("primitive_rank, address", "addr", addr.Hex(), "number", number)

	// TODO: @AC get cpchain Backend and read balance.
	coinAge, err := c.Backend.Rank(addr, number)
	if err != nil {
		log.Error("NewBasicCollector,error", "error", err, "addr", addr.Hex())
	}
	ret := new(big.Int).SetInt64(int64(coinAge))
	return common.LeftPadBytes(ret.Bytes(), 32), nil
}
