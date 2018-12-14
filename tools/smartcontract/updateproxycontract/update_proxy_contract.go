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

	"bitbucket.org/cpchain/chain/tools/smartcontract/deploy"
	"github.com/ethereum/go-ethereum/common"
)

func main() {
	proxyContractRegisterAddress := common.HexToAddress("0x1a9fae75908752d0abf4dca45ebcac311c376290")

	proxyAddress := common.HexToAddress("0x82104907aa699b2982fc46f38fd8c915d03cdb8d")
	// realAddress := common.HexToAddress("0xca53baf44e68a2f440cafee2bbcc23631ad26811") // not exist contract
	realAddress := common.HexToAddress("0xca53baf44e68a2f440cafee2bbcc23631ad2689e")

	success := deploy.UpdateRegisterProxyAddress(proxyContractRegisterAddress, proxyAddress, realAddress, "password")
	fmt.Println("update contract success:", success)

}
