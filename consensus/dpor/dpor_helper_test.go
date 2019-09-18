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
	"time"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	lru "github.com/hashicorp/golang-lru"
)

func Test_dporHelper_verifyHeader(t *testing.T) {
	t.Skip("need to redesign the unittests for dporHelper")

	dh := &defaultDporHelper{}

	extraErr1 := "0x00000000000000000000000000000000"
	fmt.Println("extraErr1:", extraErr1)

	rightExtra := "0x0000000000000000000000000000000000000000000000000000000000000000"
	rightSeal := "0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"
	rightAddr := "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"

	time1 := big.NewInt(time.Now().Unix() + 100)
	time := big.NewInt(time.Now().Unix() - 100)

	type args struct {
		c         *Dpor
		chain     consensus.ChainReader
		header    *types.Header
		parents   []*types.Header
		refHeader *types.Header
	}
	tests := []struct {
		name    string
		d       *defaultDporHelper
		args    args
		wantErr bool
	}{
		{"header.Number is nil", dh, args{header: &types.Header{Number: nil, Time: time1}}, true},

		{"header.Time error", dh, args{header: &types.Header{Number: big.NewInt(6),
			Time: time1}}, true},

		{"errInvalidCheckpointBeneficiary", dh,
			args{header: &types.Header{Number: big.NewInt(6), Time: time, Coinbase: common.HexToAddress("aaaaa")},
				c: &Dpor{config: &configs.DporConfig{TermLen: 3}}}, true},

		{"header.Extra error1", dh,
			args{
				header: &types.Header{
					Number: big.NewInt(5), Time: time, Extra: hexutil.MustDecode(string(extraErr1))},
				c: &Dpor{config: &configs.DporConfig{TermLen: 3}}}, true},

		{"errInvalidDifficulty", dh,
			args{
				header: &types.Header{
					Number: big.NewInt(7),
					Time:   time,
					Extra:  hexutil.MustDecode(string(rightExtra)),
					Dpor: types.DporSnap{
						Seal: types.HexToDporSig(rightSeal),
						Proposers: []common.Address{
							common.HexToAddress(rightAddr),
						},
					}},
				c: &Dpor{config: &configs.DporConfig{TermLen: 3}}}, true},

		{"success", dh,
			args{
				header: &types.Header{
					Number: big.NewInt(0),
					Time:   time,
					Extra:  hexutil.MustDecode(string(rightExtra)),
					Dpor: types.DporSnap{
						Seal: types.HexToDporSig(rightSeal),
						Proposers: []common.Address{
							common.HexToAddress(rightAddr),
						},
					},
				},
				c:       &Dpor{config: &configs.DporConfig{TermLen: 3}, dh: &defaultDporHelper{}},
				chain:   &FakeReader{},
				parents: []*types.Header{},
			}, false},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			dh := &defaultDporHelper{}
			if err := dh.verifyHeader(tt.args.c, tt.args.chain, tt.args.header, tt.args.parents, tt.args.refHeader, true, false); (err != nil) != tt.wantErr {
				t.Errorf("defaultDporHelper.verifyHeader(%v, %v, %v, %v, %v) error = %v, wantErr %v", tt.args.c, tt.args.chain, tt.args.header, tt.args.parents, tt.args.refHeader, err, tt.wantErr)
			}
		})
	}
}

func Test_dporHelper_verifyCascadingFields(t *testing.T) {
	t.Skip("need to redesign the unittests for dporHelper")

	recents, _ := lru.NewARC(10)
	rightExtra := "0x0000000000000000000000000000000000000000000000000000000000000000"
	seal := "0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"
	proposer := "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"
	time1 := big.NewInt(time.Now().Unix() - 100)
	time2 := big.NewInt(time.Now().Unix() + 100)
	header := &types.Header{Number: big.NewInt(0), Time: time1}
	parentHash := header.Hash()
	recents.Add(parentHash, &DporSnapshot{config: &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 3}, RecentProposers: make(map[uint64][]common.Address)})
	chain := &FakeReader{}
	type args struct {
		d         *Dpor
		chain     consensus.ChainReader
		header    *types.Header
		parents   []*types.Header
		refHeader *types.Header
	}
	tests := []struct {
		name    string
		d       *defaultDporHelper
		args    args
		wantErr bool
	}{
		{"success when block 0", &defaultDporHelper{},
			args{d: &Dpor{recentSnaps: recents, config: &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 4}},
				header: &types.Header{Number: big.NewInt(0), ParentHash: parentHash}, chain: chain}, false},
		{"fail with parent block", &defaultDporHelper{},
			args{d: &Dpor{recentSnaps: recents, config: &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 4}},
				header:  &types.Header{Number: big.NewInt(1), ParentHash: parentHash, Time: time1},
				parents: []*types.Header{header}, chain: chain}, true},
		{"errInvalidSigners", &defaultDporHelper{},
			args{d: &Dpor{recentSnaps: recents, config: &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 4}, dh: &defaultDporHelper{}},
				header: &types.Header{Number: big.NewInt(1), ParentHash: parentHash, Time: time2,
					Extra: hexutil.MustDecode(rightExtra), Dpor: types.DporSnap{Seal: types.HexToDporSig(seal),
						Proposers: []common.Address{common.HexToAddress(proposer)}},
				},
				parents: []*types.Header{header}, chain: chain}, true},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			d := &defaultDporHelper{}
			if err := d.verifyProposers(tt.args.d, tt.args.chain, tt.args.header, tt.args.parents, tt.args.refHeader); (err != nil) != tt.wantErr {
				t.Errorf("defaultDporHelper.verifyProposers(%v, %v, %v, %v, %v) error = %v, wantErr %v", tt.args.d, tt.args.chain, tt.args.header, tt.args.parents, tt.args.refHeader, err, tt.wantErr)
			}
		})
	}
}

func Test_dporHelper_snapshot(t *testing.T) {
	type args struct {
		c       *Dpor
		chain   consensus.ChainReader
		number  uint64
		hash    common.Hash
		parents []*types.Header
	}
	tests := []struct {
		name    string
		d       *defaultDporHelper
		args    args
		want    *DporSnapshot
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			d := &defaultDporHelper{}
			got, err := d.snapshot(tt.args.c, tt.args.chain, tt.args.number, tt.args.hash, tt.args.parents)
			if (err != nil) != tt.wantErr {
				t.Errorf("defaultDporHelper.Snapshot(%v, %v, %v, %v, %v) error = %v, wantErr %v", tt.args.c, tt.args.chain, tt.args.number, tt.args.hash, tt.args.parents, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("defaultDporHelper.Snapshot(%v, %v, %v, %v, %v) = %v, want %v", tt.args.c, tt.args.chain, tt.args.number, tt.args.hash, tt.args.parents, got, tt.want)
			}
		})
	}
}

func Test_dporHelper_verifySeal(t *testing.T) {

	rightExtra := "0x0000000000000000000000000000000000000000000000000000000000000000"
	rightAddr := "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"
	rightSeal := "0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"

	time1 := big.NewInt(time.Now().Unix() - 100)

	header := &types.Header{Number: big.NewInt(0), Time: time1}
	parentHash := header.Hash()
	recents, _ := lru.NewARC(10)
	recents.Add(parentHash, &DporSnapshot{})
	//rightExtra2 := "0x00c9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00c9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00c9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"

	type args struct {
		c         *Dpor
		chain     consensus.ChainReader
		header    *types.Header
		parents   []*types.Header
		refHeader *types.Header
	}
	tests := []struct {
		name    string
		d       *defaultDporHelper
		args    args
		wantErr bool
	}{
		// TODO: Add test cases.
		{"fail when block number is 0", &defaultDporHelper{},
			args{
				c: &Dpor{
					config:      &configs.DporConfig{Period: 3},
					db:          &fakeDb{1},
					recentSnaps: recents, dh: &defaultDporHelper{}},
				chain: &FakeReader{},
				header: &types.Header{
					Number: big.NewInt(0),
					Time:   time1,
					Extra:  hexutil.MustDecode(string(rightExtra)),
					Dpor: types.DporSnap{
						Proposers: []common.Address{
							common.HexToAddress(rightAddr),
						},
						Seal: types.HexToDporSig(rightSeal),
					},
				}},
			true},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if err := tt.d.verifySeal(tt.args.c, tt.args.chain, tt.args.header, tt.args.parents, tt.args.refHeader); (err != nil) != tt.wantErr {
				t.Errorf("defaultDporHelper.verifySeal(%v, %v, %v, %v, %v) error = %v, wantErr %v", tt.args.c, tt.args.chain, tt.args.header, tt.args.parents, tt.args.refHeader, err, tt.wantErr)
			}
		})
	}
}

func Test_defaultDporHelper_verifyBasicImpeach(t *testing.T) {
	addr, _ := getTestAccount()

	tx1 := types.NewTransaction(0, common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"), big.NewInt(10), 50000, big.NewInt(10), nil)
	tx1, _ = tx1.WithSignature(types.HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))
	newHeader := &types.Header{
		ParentHash:   common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		Coinbase:     common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"),
		StateRoot:    common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxsRoot:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptsRoot: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Number:       big.NewInt(1),
		GasLimit:     uint64(3141592),
		GasUsed:      uint64(21000),
		Time:         big.NewInt(1426516743),
		Extra:        hexutil.MustDecode("0x0000000000000000000000000000000000000000000000000000000000000000"),
		Dpor: types.DporSnap{
			Proposers: []common.Address{
				addr,
			},
			Sigs:       make([]types.DporSignature, 3),
			Validators: []common.Address{},
		},
	}

	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	d.chain = newBlockchain(888)
	d.dh = dph
	err := dph.verifyBasicImpeach(d, d.chain, newHeader, newHeader)
	errInvalidImpeachErr := errors.New("invalid impeach txs root")
	equalSigner := reflect.DeepEqual(err, errInvalidImpeachErr)
	if !equalSigner {
		t.Error("Call verifyBasicImpeach failed...")
	}
}

func Test_defaultDporHelper_snapshot(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	d.chain = newBlockchain(888)
	d.dh = dph
	snapshot := NewSnapshot(&configs.DporConfig{Period: 3, TermLen: 4, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	d.SetCurrentSnap(snapshot)
	snap, err := d.dh.snapshot(d, d.chain, 827, d.CurrentSnap().hash(), nil)
	if snap != d.CurrentSnap() || err != nil {
		t.Error("Call snapshot failed...")
	}
}

func Test_defaultDporHelper_verifyHeader(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	d.mode = FakeMode
	d.chain = newBlockchain(888)
	d.dh = dph
	genesis := d.chain.GetHeaderByNumber(0)
	err := d.dh.verifyHeader(d, d.chain, genesis, nil, newHeader(), true, true)
	if err != nil {
		t.Error("Call verifyHeader failed...")
	}
	err1 := dph.verifyBasic(d, d.chain, genesis, nil, newHeader())
	if err1 != nil {
		t.Error("Call verifyBasic failed...")
	}
	err2 := d.dh.verifySignatures(d, d.chain, newHeader(), nil, nil)
	if err2 != nil {
		t.Error("Call verifySignatures failed...")
	}

}

func Test_defaultDporHelper_verifyBasic(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.mode = FakeMode
	d.chain = newBlockchain(888)
	d.dh = dph
	// Check status
	err1 := dph.verifyBasic(d, d.chain, newHeader(), nil, nil)
	fmt.Println(err1)
	if err1 != nil {
		t.Error("Call ValidateBlock check status failed...")
	}
	// Check Parent header:
	d.mode = NormalMode
	err2 := d.dh.verifyBasic(d, d.chain, newHeader(), nil, nil)
	errUnknownAncestor := errors.New("unknown ancestor")
	equalSigner := reflect.DeepEqual(err2, errUnknownAncestor)
	if !equalSigner {
		t.Error("Call ValidateBlock failed...")
	}
}

func Test_defaultDporHelper_validateBlock(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.mode = FakeMode
	d.chain = newBlockchain(888)
	d.dh = dph
	unknownBlock := types.NewBlock(&types.Header{GasLimit: configs.DefaultGasLimitPerBlock}, nil, nil)
	err1 := d.dh.validateBlock(d, d.chain, unknownBlock, true, true)
	err2 := d.dh.verifyHeader(d, d.chain, unknownBlock.Header(), nil, unknownBlock.RefHeader(), true, true)
	err3 := d.chain.ValidateBlockBody(unknownBlock)
	equalSigner1 := reflect.DeepEqual(err1, err2)
	equalSigner2 := reflect.DeepEqual(err1, err3)
	if equalSigner1 && (!equalSigner2) {
		t.Error("Call validateBlock failed...")
	}
}

func Test_defaultDporHelper_verifyDporSnapImpeach(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.mode = FakeMode
	d.chain = newBlockchain(888)
	d.dh = dph
	// Parent is empty:
	err := dph.verifyDporSnapImpeach(d, d.chain, newHeader(), nil, nil)
	errUnknownAncestor := errors.New("unknown ancestor")
	equalSigner := reflect.DeepEqual(err, errUnknownAncestor)
	if !equalSigner {
		t.Error("Call verifyDporSnapImpeach failed...")
	}

}

func Test_defaultDporHelper_verifyProposers(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.mode = FakeMode
	d.chain = newBlockchain(888)
	d.dh = dph
	// dpor number is 0
	header := newHeader()
	header.Number = big.NewInt(0)
	err1 := dph.verifyProposers(d, d.chain, header, nil, nil)
	if err1 != nil {
		t.Error("Call verifyProposers failed... ")
	}
}

func Test_defaultDporHelper_verifySeal(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.mode = FakeMode
	d.chain = newBlockchain(888)
	d.dh = dph
	header := newHeader()
	// dpor number is 0:
	header.Number = big.NewInt(0)
	errUnknown := errors.New("unknown block")
	err1 := dph.verifySeal(d, d.chain, header, nil, nil)
	equalSigner := reflect.DeepEqual(err1, errUnknown)
	if !equalSigner {
		t.Error("Call verifySeal failed,,,")
	}
	// Check status:
	d.mode = FakeMode
	err2 := dph.verifySeal(d, d.chain, newHeader(), nil, nil)
	if err2 != nil {
		t.Error("Call verifySeal check status failed,,,")
	}
}

func Test_defaultDporHelper_verifySignatures(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.mode = FakeMode
	d.chain = newBlockchain(888)
	d.dh = dph
	header := newHeader()
	// dpor number is 0:
	header.Number = big.NewInt(0)
	errUnknown := errors.New("unknown block")
	err1 := dph.verifySignatures(d, d.chain, header, nil, nil)
	equalSigner := reflect.DeepEqual(err1, errUnknown)
	if !equalSigner {
		t.Error("Call verifySignatures failed,,,")
	}
	// Check status:
	d.mode = FakeMode
	err2 := dph.verifySignatures(d, d.chain, newHeader(), nil, nil)
	if err2 != nil {
		t.Error("Call verifySignatures check status failed,,,")
	}
}

func Test_defaultDporHelper_signHeader(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.mode = FakeMode
	d.chain = newBlockchain(888)
	header := newHeader()
	d.dh = dph
	errInvalidState := errors.New("the state is unexpected for signing header")
	err := dph.signHeader(d, d.chain, header, consensus.Idle)
	equalSigner := reflect.DeepEqual(err, errInvalidState)
	if !equalSigner {
		t.Error("Call signerHeader check status failed...")
	}
}
