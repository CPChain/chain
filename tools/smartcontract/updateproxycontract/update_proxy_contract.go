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

package main

import (
	"fmt"
	"math/big"
	"os"

	"bitbucket.org/cpchain/chain/tools/smartcontract/deploy"
	"github.com/ethereum/go-ethereum/common"
)

// upgrade proxy contract, can only be executed locally
func main() {
	if len(os.Args) < 4 {
		fmt.Println("Error! Need 3 contract address:<proxyContractRegisterAddress> <proxyAddress> <realAddress>\nexample:env CPCHAIN_KEYSTORE_FILEPATH=/cpchain/keystore/ ./updateproxycontract 0x1a9fae75908752d0abf4dca45ebcac311c376290 0x82104907aa699b2982fc46f38fd8c915d03cdb8d 0xca53baf44e68a2f440cafee2bbcc23631ad2689e")
		return
	}
	fmt.Println("proxyContractRegisterAddress :", os.Args[1])
	fmt.Println("proxyAddress                 :", os.Args[2])
	fmt.Println("realAddress                  :", os.Args[3])

	proxyContractRegisterAddress := common.HexToAddress(os.Args[1])
	proxyAddress := common.HexToAddress(os.Args[2])
	realAddress := common.HexToAddress(os.Args[3])

	// get latest nonce
	nonce := big.NewInt(-1)
	success := deploy.UpdateRegisterProxyAddress("[Proxy Contract Upgrade]", proxyContractRegisterAddress, proxyAddress, realAddress, "password", nonce)
	fmt.Println("update contract success:", success)

}
