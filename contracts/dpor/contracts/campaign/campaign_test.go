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

package campaign_test

import (
	"crypto/ecdsa"
	"fmt"
	"os"
	"path/filepath"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"
	"github.com/ethereum/go-ethereum/crypto"
)

func TestCampaignCandidateInfoOf(t *testing.T) {
	t.Skip("we shall use a simulated backend.")

	// create client.
	client, err := cpclient.Dial("http://localhost:8501") // local
	if err != nil {
		log.Fatal(err.Error())
	}

	file, _ := os.Open("../../../../examples/cpchain/data/data1/keystore/")
	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	kst := keystore.NewKeyStore(keyPath, 2, 1)
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, "password")
	privateKey := key.PrivateKey

	if err != nil {
		log.Fatal(err.Error())
	}

	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		log.Fatal("error casting public key to ECDSA")
	}

	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	// launch contract deploy transaction.
	address := configs.ChainConfigInfo().Dpor.Contracts[configs.ContractCampaign]

	instance, err := campaign.NewCampaign(address, client)
	if err != nil {
		log.Error("err", "error", err)
		return
	}

	// test contract map variable call.
	numOfCampaign, deposit, startViewIdx, endViewIdx, err := instance.CandidateInfoOf(nil, fromAddress)
	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("candidate info of", fromAddress.Hex(), ":", numOfCampaign, deposit, startViewIdx, endViewIdx)
}
