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
	"bitbucket.org/cpchain/chain/configs"
	"github.com/ethereum/go-ethereum/common"
)

//go:generate abigen --sol ../contracts/primitive_contracts.sol --pkg contracts --out ../contracts/primitive_contracts.go

// Definitions of primitive contracts
//

// GetProxyCount returns the count of transactions processed by the proxy specified by given account address
type GetProxyCount struct {
	Backend RptPrimitiveBackend
}

func (c *GetProxyCount) RequiredGas(input []byte) uint64 {
	return configs.IsProxyGas
}

func (c *GetProxyCount) Run(input []byte) ([]byte, error) {
	addr, number, err := extractRptPrimitivesArgs(input)
	if err != nil {
		log.Warnf("primitive_proxy_count got error %v", err)
		return common.LeftPadBytes(new(big.Int).Bytes(), 32), nil
	}
	log.Info("primitive_proxy_count", "address", addr.Hex(), "block number", number)

	// TODO: @AC get cpchain Backend and read balance.
	_, proxyCount, err := c.Backend.ProxyInfo(addr, number)
	if err != nil {
		log.Warn("NewBasicCollector,error", "error", err, "address", addr.Hex())
		return common.LeftPadBytes(new(big.Int).Bytes(), 32), nil
	}
	ret := new(big.Int).SetInt64(int64(proxyCount))
	return common.LeftPadBytes(ret.Bytes(), 32), nil
}

type IsProxy struct {
	Backend RptPrimitiveBackend
}

func (c *IsProxy) RequiredGas(input []byte) uint64 {
	return configs.IsProxyGas
}

func (c *IsProxy) Run(input []byte) ([]byte, error) {
	addr, number, err := extractRptPrimitivesArgs(input)
	if err != nil {
		log.Error("primitive_is_proxy got error", "error", err)
		return common.LeftPadBytes(new(big.Int).Bytes(), 32), nil
	}
	log.Info("primitive_is_proxy", "address", addr.Hex(), "number", number)

	isProxy, _, err := c.Backend.ProxyInfo(addr, number)
	if err != nil {
		log.Error("NewBasicCollector,error", "error", err, "address", addr.Hex())
		ret := new(big.Int).SetInt64(int64(0))
		return common.LeftPadBytes(ret.Bytes(), 32), nil
	}
	ret := new(big.Int).SetInt64(int64(isProxy))
	return common.LeftPadBytes(ret.Bytes(), 32), nil
}
