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

package deploy

import (
	"context"
	"fmt"
	"testing"

	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/ethereum/go-ethereum/common"
)

func TestMainnetInitContract(t *testing.T) {
	t.Skip("skip contract verify test")

	client, err := cpclient.Dial("http://localhost:8501")
	if err != nil {
		log.Fatal(err.Error())
		t.Skip("skip mainnet init verify contract")
	}
	ctx := context.Background()

	// admission.go
	// addr := common.HexToAddress("0x3DCe838fded8631E1CcBC6373121d83e0a3C7dCD")// proxy
	// addr := common.HexToAddress("0xe691f6C6688f109102E04253d6FA55497238bA57") // real

	// campaign
	// addr := common.HexToAddress("0x34eF33413C6578611CF39A9b8d59D5f1e724f240") // proxy
	addr := common.HexToAddress("0xED111e097C77253bc0febBd7e85F5Af6D60A8196") // real

	code, err := client.CodeAt(ctx, addr, nil)
	if len(code) > 0 {
		fmt.Println("contract code exist")
	} else {
		fmt.Println("contract code not exist")
	}
	if err != nil {
		println("DeployContract failed")
		log.Fatal(err.Error())
	}
}

func TestDevInitContract(t *testing.T) {
	t.Skip("skip contract verify test")

	// client, err, _, _, fromAddress := config.Connect("password")
	client, err := cpclient.Dial("http://localhost:8501")
	if err != nil {
		log.Fatal(err.Error())
		t.Skip("skip dev init verify contract")
	}
	ctx := context.Background()

	// devProxyContractRegister = common.HexToAddress("0x1a9fae75908752d0abf4dca45ebcac311c376290")
	devContractAddressMap := map[string]common.Address{
		"ContractProposer":   common.HexToAddress("0x310236762f36bf0f69f792bd9fb08b5c679aa3f1"),
		"ContractReward":     common.HexToAddress("0xd6E4BdCc9b4D1744Cf16Ce904B9EDE5e78751002"),
		"ContractAdmission":  common.HexToAddress("0x0DDf4057eeDFb80D58029Be49bab09bbc45bC500"),
		"ContractCampaign":   common.HexToAddress("0x82104907AA699b2982Fc46f38Fd8C915d03Cdb8d"),
		"ContractRpt":        common.HexToAddress("0x019cC04ff9d88529b9e58FF26bfc53BcE060e915"),
		"ContractRegister":   common.HexToAddress("0xaAae743244a7A5116470df8BD398e7D562ae8881"),
		"ContractPdash":      common.HexToAddress("0xd81ab6B1e656550F90B2d874926B949fde97096D"),
		"ContractPdashProxy": common.HexToAddress("0xD791F193C2F374f49bCbcf20750749b7AF17204e"),
	}

	for name, addr := range devContractAddressMap {
		fmt.Println("contract name:", name)
		fmt.Println("addr:", addr.Hex())
		code, err := client.CodeAt(ctx, addr, nil)
		if len(code) > 0 {
			fmt.Println("contract code exist")
		} else {
			fmt.Println("contract code not exist")
		}
		if err != nil {
			println("DeployContract failed:" + name)
			log.Fatal(err.Error())
		}
	}
}
