// Copyright 2014 The go-ethereum Authors
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

package vm

import (
	"fmt"

	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/crypto"
	"bitbucket.org/cpchain/chain/log"
)

var (
	emptyAddress = common.Address{}
)

// get real logic contract address by proxy contract address
func GetRealContractAddress(evm *EVM, caller ContractRef, proxyContractAddress common.Address, gas uint64) common.Address {
	log.Debug("GetRealContractAddress", "proxyContractAddress", proxyContractAddress.Hex())
	realAddress := proxyContractAddress

	if dc := evm.chainConfig.Dpor; dc != nil {
		if proxyRegister := dc.ProxyContractRegister; proxyRegister != emptyAddress {
			// setup param from #getContractInput(methodSignature,proxyAddress)
			paramBytes := getContractInput(proxyContractAddress)
			if ret, _, err := evm.StaticCall(caller, proxyRegister, paramBytes, gas); err == nil {
				// get real contract address parse from ret
				address := common.BytesToAddress(ret)
				log.Debug("GetRealContractAddress ", "hex(address)", common.Bytes2Hex(ret), "address", address.Hex())

				if address != emptyAddress {
					log.Debug("parseAddress ok", "realAddress", realAddress.Hex())
					realAddress = address
				}
			} else {
				log.Warn("GetRealContractAddress", "err", err)
			}
		}
	}

	log.Debug("GetRealContractAddress", "realAddress", realAddress.Hex())
	return realAddress
}

// invoke contract method in proxyContractRegister.sol#getRealContract
func getContractInput(proxyContract common.Address) []byte {
	methodSignBytes := []byte("getRealContract(address)")
	bytes := crypto.Keccak256(methodSignBytes)
	methodSignature := fmt.Sprintf("%v", common.Bytes2Hex(bytes)[0:8])
	addrBytes := fmt.Sprintf("%064v\n", common.Bytes2Hex(proxyContract.Bytes()))
	return common.Hex2Bytes(methodSignature + addrBytes)
}
