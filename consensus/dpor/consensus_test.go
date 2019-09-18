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
