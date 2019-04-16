// Copyright 2018 The cpchain authors

package vm

import (
	"fmt"
	"time"

	"bitbucket.org/cpchain/chain/commons/cache"
	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	forceLookupTTL      = 5 * time.Second
	emptyAddress        = common.Address{}
	contractLookupCache = cache.NewLRUExpireCache(200)
)

// get real logic contract address by proxy contract address
func GetRealContractAddress(evm *EVM, caller ContractRef, proxyContractAddress common.Address, gas uint64) common.Address {
	realAddress := proxyContractAddress

	if dc := evm.chainConfig.Dpor; dc != nil {
		if proxyRegister := dc.ProxyContractRegister; proxyRegister != emptyAddress {
			// lookup in cache
			realContractFromCache, gotIt := contractLookupCache.Get(proxyContractAddress)
			if gotIt {
				log.Debug("get real address from cache for", "proxyContractAddress", proxyContractAddress.Hex())
				return realContractFromCache.(common.Address)
			}

			// setup param from #getContractInput(methodSignature,proxyAddress)
			paramBytes := getContractInput(proxyContractAddress)
			if ret, _, err := evm.StaticCall(caller, proxyRegister, paramBytes, gas); err == nil {
				// get real contract address parse from ret
				address := common.BytesToAddress(ret)
				if address != emptyAddress {
					log.Debug("GetRealContractAddress ", "hex(address)", common.Bytes2Hex(ret), "address", address.Hex())
				}

				if address != emptyAddress {
					log.Debug("parseAddress ok", "realAddress", realAddress.Hex())
					realAddress = address
					contractLookupCache.Add(proxyContractAddress, realAddress, forceLookupTTL)
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
	// the name is in line with the one in the contract
	methodSignBytes := []byte("getRealContract(address)")
	bytes := crypto.Keccak256(methodSignBytes)
	methodSignature := fmt.Sprintf("%v", common.Bytes2Hex(bytes)[0:8])
	addrBytes := fmt.Sprintf("%064v\n", common.Bytes2Hex(proxyContract.Bytes()))
	return common.Hex2Bytes(methodSignature + addrBytes)
}
