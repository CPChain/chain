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

package dpor

import (
	"errors"
	"fmt"
	"math/big"
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/stretchr/testify/assert"
)

func TestDpor_VerifyHeader(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.chain = newBlockchain(888)
	d.dh = dph
	header := newHeader()
	genesis := d.chain.GetHeaderByNumber(0)
	err := d.VerifyHeader(d.chain, genesis, true, header)
	if err != nil {
		t.Error("Call Verifyheader failed...")
	}
}

func TestDpor_VerifyHeaders(t *testing.T) {
	tests := []struct {
		name          string
		verifySuccess bool
		wantErr       bool
	}{
		{"verifyHeader success", true, true},
		{"verifyHeader failed", false, false},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				dh: &fakeDporHelper{verifySuccess: tt.verifySuccess},
			}
			_, results := c.VerifyHeaders(
				&FakeReader{},
				[]*types.Header{newHeader()},
				[]bool{true},
				[]*types.Header{newHeader()})

			got := <-results
			fmt.Println("got:", got)
			if tt.wantErr != (got == nil) {
				t.Errorf("Dpor.VerifyHeaders() got = %v, want %v", got, tt.wantErr)
			}
		})
	}
}

func TestDpor_APIs(t *testing.T) {
	c := &Dpor{
		dh: &fakeDporHelper{},
	}
	got := c.APIs(nil)
	assert.Equal(t, 1, len(got), "only 1 api should be created")
}

func TestDpor_Author(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.chain = newBlockchain(888)
	d.dh = dph
	header := newHeader()
	_, err := d.Author(header)
	if err != nil {
		t.Error("Call Author failed...")
	}
}

func TestDpor_VerifySeal(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.chain = newBlockchain(888)
	d.dh = dph
	d.mode = FakeMode
	header := newHeader()
	err := d.VerifySeal(d.chain, header, nil)
	if err != nil {
		t.Error("Call verify seal failed...")
	}
}

func TestDpor_VerifySigs(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.chain = newBlockchain(888)
	d.dh = dph
	d.mode = FakeMode
	header := newHeader()
	err := d.VerifySigs(d.chain, header, nil)
	if err != nil {
		t.Error("Call verify seal failed...")
	}
}

func TestDpor_PrepareBlock(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.chain = newBlockchain(888)
	d.dh = dph
	header := newHeader()
	header.ParentHash = d.currentSnap.Hash
	header.Dpor.Proposers = proposers
	header.Number = big.NewInt(828)
	err := d.PrepareBlock(d.chain, header)
	errUnknownAnc := errors.New("unknown ancestor")
	equalSigner := reflect.DeepEqual(err, errUnknownAnc)
	if !equalSigner {
		t.Error("Call PrepareBlock failed...")
	}
}

func TestDpor_GetBlockReward(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 7, common.Hash{}, proposers, nil, FakeMode)
	d.chain = newBlockchain(888)
	d.dh = dph
	a := d.GetBlockReward(38298)
	b := d.GetBlockReward(25233333333333333)
	equalSigner := reflect.DeepEqual(a, b)
	if equalSigner {
		t.Error("Call GetBlockchain failed...")
	}
}

func TestDpor_BlockRewardOfMainnet(t *testing.T) {
	var (
		mainnetBlockPeriod = 1e4 // 10000 mill 10 second
		cep1BlocksPerDay   = 24 * 60 * 60 * 1000 / int64(mainnetBlockPeriod)

		// Blocks produce per day
		cep1BlocksY1 = 366 * cep1BlocksPerDay // contain a leap day
		cep1BlocksY2 = 365 * cep1BlocksPerDay
		cep1BlocksY3 = 365 * cep1BlocksPerDay
		cep1BlocksY4 = 365 * cep1BlocksPerDay
		cep1BlocksY5 = 366 * cep1BlocksPerDay

		// supply yearly
		cep1BlockRewardSupplyY1 = new(big.Int).Mul(big.NewInt(40002336), big.NewInt(1e+18))
		cep1BlockRewardSupplyY2 = new(big.Int).Mul(big.NewInt(29990736), big.NewInt(1e+18))
		cep1BlockRewardSupplyY3 = new(big.Int).Mul(big.NewInt(22485168), big.NewInt(1e+18))
		cep1BlockRewardSupplyY4 = new(big.Int).Mul(big.NewInt(16997904), big.NewInt(1e+18))
		cep1BlockRewardSupplyY5 = new(big.Int).Mul(big.NewInt(127438272), big.NewInt(1e+17))

		// block reward
		cep1BlockRewardY1 = new(big.Int).Div(cep1BlockRewardSupplyY1, big.NewInt(cep1BlocksY1)) // reward 12.65 cpc per block
		cep1BlockRewardY2 = new(big.Int).Div(cep1BlockRewardSupplyY2, big.NewInt(cep1BlocksY2)) // reward 9.51 cpc per block
		cep1BlockRewardY3 = new(big.Int).Div(cep1BlockRewardSupplyY3, big.NewInt(cep1BlocksY3)) // reward 7.13 cpc per block
		cep1BlockRewardY4 = new(big.Int).Div(cep1BlockRewardSupplyY4, big.NewInt(cep1BlocksY4)) // reward 5.39 cpc per block
		cep1BlockRewardY5 = new(big.Int).Div(cep1BlockRewardSupplyY5, big.NewInt(cep1BlocksY5)) // reward 4.03 cpc per block
	)
	t.Log(cep1BlockRewardY2)
	t.Log(cep1BlockRewardY3)
	t.Log(cep1BlockRewardY4)
	t.Log(cep1BlockRewardY5)

	// main test
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 7, common.Hash{}, proposers, nil, FakeMode)
	d.chain = newBlockchain(888)
	d.dh = dph

	// 1 year
	y1 := d.GetBlockReward(uint64(cep1BlocksY1))
	if y1.Cmp(cep1BlockRewardY1) != 0 {
		t.Errorf("got reward is not equal with expect, %v != %v", y1, cep1BlockRewardY1)
	}

	// 2 year
	t.Logf("Reduced at: %d", cep1BlocksY1+cep1BlocksY2)
	y2 := d.GetBlockReward(uint64(cep1BlocksY1 + cep1BlocksY2))
	if y2.Cmp(cep1BlockRewardY2) != 0 {
		t.Errorf("got reward is not equal with expect, %v != %v", y2, cep1BlockRewardY2)
	}

	// 3 year
	y3 := d.GetBlockReward(uint64(cep1BlocksY1 + cep1BlocksY2 + cep1BlocksY3))
	if y3.Cmp(cep1BlockRewardY3) != 0 {
		t.Errorf("got reward is not equal with expect, %v != %v", y3, cep1BlockRewardY3)
	}

	// 4 year
	y4 := d.GetBlockReward(uint64(cep1BlocksY1 + cep1BlocksY2 + cep1BlocksY3 + cep1BlocksY4))
	if y4.Cmp(cep1BlockRewardY4) != 0 {
		t.Errorf("got reward is not equal with expect, %v != %v", y4, cep1BlockRewardY4)
	}

	// 5 year
	y5 := d.GetBlockReward(uint64(cep1BlocksY1 + cep1BlocksY2 + cep1BlocksY3 + cep1BlocksY4 + cep1BlocksY5))
	if y5.Cmp(cep1BlockRewardY5) != 0 {
		t.Errorf("got reward is not equal with expect, %v != %v", y5, cep1BlockRewardY5)
	}

	// 6 year
	y6 := d.GetBlockReward(uint64(cep1BlocksY1 + cep1BlocksY2 + cep1BlocksY3 + cep1BlocksY4 + cep1BlocksY5 + 1))
	if y6.Int64() != 0 {
		t.Errorf("got reward is not equal with expect, %v != %v", y6, 0)
	}
}

func TestDpor_Seal(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 7, common.Hash{}, proposers, nil, FakeMode)
	d.chain = newBlockchain(888)
	d.dh = dph
	privKeyInHex := "fad9c8855b740a0b7ed4c221dbad0f33a83a49cad6b3fe8d5817ac83d38b6a19"
	privateKey, _ := crypto.HexToECDSA(privKeyInHex)
	signFn := func(account accounts.Account, hash []byte) ([]byte, error) {
		return crypto.Sign(hash, privateKey)
	}
	addr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 66))
	d.Authorize(addr, signFn)
	// Step 1: Check number
	header := newHeader()
	header.Number = big.NewInt(0)
	unknownBlock := types.NewBlock(header, nil, nil)
	seal1, _ := d.Seal(d.chain, unknownBlock, nil)
	if seal1 != nil {
		t.Error("Call Seal failed...")
	}
	// Step 2: Check period
	config := &configs.DporConfig{Period: 0, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}
	d.config = config
	seal2, _ := d.Seal(d.chain, unknownBlock, nil)
	if seal2 != nil {
		t.Error("Call Seal failed...")
	}
}
