// Copyright 2017 The go-ethereum Authors
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

// Package dpor implements the dpor consensus engine.
package dpor

import (
	"math/big"
	"reflect"
	"sync"
	"testing"

	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/params"
	"github.com/hashicorp/golang-lru"
)

var (
	addr1 = common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465")
	addr2 = common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092")
	addr3 = common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")
	addr4 = common.HexToAddress("0x3333333333333333333333333333333333333333")
)

func getSignerAddress() []common.Address {
	signersAddr := make([]common.Address, 3)
	signersAddr[0] = addr1
	signersAddr[1] = addr2
	signersAddr[2] = addr3
	return signersAddr
}

func getCandidates() []common.Address {
	return getSignerAddress()
}

func getRecents() map[uint64]common.Address {
	signers := make(map[uint64]common.Address)
	signers[0] = addr1
	signers[1] = addr2
	return signers
}

func Test_percentagePBFT(t *testing.T) {
	type args struct {
		n uint
		N uint
	}
	tests := []struct {
		name string
		args args
		want bool
	}{
		{"3*0>21*2", args{0, 21}, false},
		{"3*14>21*2", args{14, 21}, false},
		{"3*15>21*2", args{15, 21}, true},
		{"3*21>21*2", args{21, 21}, true},
		{"3*1000>21*2", args{1000, 21}, true},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := percentagePBFT(tt.args.n, tt.args.N); got != tt.want {
				t.Errorf("percentagePBFT() = %v, want %v", got, tt.want)
			}
		})
	}
}

func Test_sigHash(t *testing.T) {
	tx1 := types.NewTransaction(0, common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"), big.NewInt(10), 50000, big.NewInt(10), nil)
	tx1, _ = tx1.WithSignature(types.HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))
	newHeader := &types.Header{
		ParentHash:  common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		UncleHash:   common.HexToHash("0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"),
		Coinbase:    common.HexToAddress("0x8888f1F195AFa192CfeE860698584c030f4c9dB1"),
		Root:        common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxHash:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptHash: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Difficulty:  big.NewInt(131072),
		Number:      big.NewInt(1),
		GasLimit:    uint64(3141592),
		GasUsed:     uint64(21000),
		Time:        big.NewInt(1426516743),
		Extra:       []byte("0x0000000000000000000000000000000000000000000000000000000000000000e94b7b6c5a0e526a4d97f9768ad6097bde25c62ac05302acebd0730e3a18a058d7d1cb1204c4a092ef3dd127de235f15ffb4fc0d71469d1339df64650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"),
		//Extra2:      []byte("ext2"),
		MixDigest: common.HexToHash("bd4472abb6659ebe3ee06ee4d7b72a00a9f4d001caca51342001075469aff498"),
		Nonce:     types.EncodeNonce(uint64(0xa13a5a8c8f2bb1c4)),
	}

	type args struct {
		header *types.Header
	}
	tests := []struct {
		name     string
		args     args
		wantHash common.Hash
	}{
		{"sigHash", args{newHeader}, common.HexToHash("0x8842a173b6a10d45d1705bedcb1644755075e2a78258bd7bca4011719d0d91b4")},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if gotHash := sigHash(tt.args.header); !reflect.DeepEqual(gotHash, tt.wantHash) {
				t.Errorf("sigHash(%v) = %v, want %v", tt.args.header, gotHash, tt.wantHash)
			}
		})
	}
}

func Test_ecrecover(t *testing.T) {
	tx1 := types.NewTransaction(0, common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"), big.NewInt(10), 50000, big.NewInt(10), nil)
	tx1, _ = tx1.WithSignature(types.HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))
	newHeader := &types.Header{
		ParentHash:  common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		UncleHash:   common.HexToHash("0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"),
		Coinbase:    common.HexToAddress("0x8888f1F195AFa192CfeE860698584c030f4c9dB1"),
		Root:        common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxHash:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptHash: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Difficulty:  big.NewInt(131072),
		Number:      big.NewInt(1),
		GasLimit:    uint64(3141592),
		GasUsed:     uint64(21000),
		Time:        big.NewInt(1426516743),
		Extra:       []byte("0x0000000000000000000000000000000000000000000000000000000000000000e94b7b6c5a0e526a4d97f9768ad6097bde25c62ac05302acebd0730e3a18a058d7d1cb1204c4a092ef3dd127de235f15ffb4fc0d71469d1339df64650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"),
		Extra2:      []byte("0x0000000000000000000000000000000000000000000000000000000000000000e94b7b6c5a0e526a4d97f9768ad6097bde25c62ac05302acebd0730e3a18a058d7d1cb1204c4a092ef3dd127de235f15ffb4fc0d71469d1339df64650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"),
		MixDigest:   common.HexToHash("bd4472abb6659ebe3ee06ee4d7b72a00a9f4d001caca51342001075469aff498"),
		Nonce:       types.EncodeNonce(uint64(0xa13a5a8c8f2bb1c4)),
	}
	cache, _ := lru.NewARC(10)

	//addresses := []common.Address{common.HexToAddress("0x8842a173b6a10d45d1705bedcb1644755075e2a78258bd7bca4011719d0d91b4")}

	type args struct {
		header   *types.Header
		sigcache *lru.ARCCache
	}
	tests := []struct {
		name    string
		args    args
		want    common.Address
		want1   []common.Address
		wantErr bool
	}{
		{"ecrecover failed", args{newHeader, cache}, common.Address{}, []common.Address{}, true},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, got1, err := ecrecover(tt.args.header, tt.args.sigcache)
			if (err != nil) != tt.wantErr {
				t.Errorf("ecrecover(%v, %v) error = %v, wantErr %v", tt.args.header, tt.args.sigcache, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("ecrecover got = %v, want %v", got, tt.want)
				//t.Errorf("ecrecover(%v, %v) got = %v, want %v", tt.args.header, tt.args.sigcache, got, tt.want)
			}
			if !reflect.DeepEqual(got1, tt.want1) {
				t.Errorf("ecrecover got1 = %v, want %v", got1, tt.want1)
				//t.Errorf("ecrecover(%v, %v) got1 = %v, want %v", tt.args.header, tt.args.sigcache, got1, tt.want1)
			}
		})
	}
}

func TestDpor_VerifyHeader(t *testing.T) {
	type fields struct {
		config       *params.DporConfig
		db           ethdb.Database
		recents      *lru.ARCCache
		signatures   *lru.ARCCache
		signedBlocks map[uint64]common.Hash
		signer       common.Address
		signFn       SignerFn
		lock         sync.RWMutex
	}
	type args struct {
		chain     consensus.ChainReader
		header    *types.Header
		seal      bool
		refHeader *types.Header
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				config:       tt.fields.config,
				db:           tt.fields.db,
				recents:      tt.fields.recents,
				signatures:   tt.fields.signatures,
				signedBlocks: tt.fields.signedBlocks,
				signer:       tt.fields.signer,
				signFn:       tt.fields.signFn,
				lock:         tt.fields.lock,
			}
			if err := c.VerifyHeader(tt.args.chain, tt.args.header, tt.args.seal, tt.args.refHeader); (err != nil) != tt.wantErr {
				t.Errorf("Dpor.VerifyHeader(%v, %v, %v, %v) error = %v, wantErr %v", tt.args.chain, tt.args.header, tt.args.seal, tt.args.refHeader, err, tt.wantErr)
			}
		})
	}
}

func TestDpor_VerifyHeaders(t *testing.T) {
	type fields struct {
		config       *params.DporConfig
		db           ethdb.Database
		recents      *lru.ARCCache
		signatures   *lru.ARCCache
		signedBlocks map[uint64]common.Hash
		signer       common.Address
		signFn       SignerFn
		lock         sync.RWMutex
	}
	type args struct {
		chain      consensus.ChainReader
		headers    []*types.Header
		seals      []bool
		refHeaders []*types.Header
	}
	tests := []struct {
		name   string
		fields fields
		args   args
		want   chan<- struct{}
		want1  <-chan error
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				config:       tt.fields.config,
				db:           tt.fields.db,
				recents:      tt.fields.recents,
				signatures:   tt.fields.signatures,
				signedBlocks: tt.fields.signedBlocks,
				signer:       tt.fields.signer,
				signFn:       tt.fields.signFn,
				lock:         tt.fields.lock,
			}
			got, got1 := c.VerifyHeaders(tt.args.chain, tt.args.headers, tt.args.seals, tt.args.refHeaders)
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("Dpor.VerifyHeaders(%v, %v, %v, %v) got = %v, want %v", tt.args.chain, tt.args.headers, tt.args.seals, tt.args.refHeaders, got, tt.want)
			}
			if !reflect.DeepEqual(got1, tt.want1) {
				t.Errorf("Dpor.VerifyHeaders(%v, %v, %v, %v) got1 = %v, want %v", tt.args.chain, tt.args.headers, tt.args.seals, tt.args.refHeaders, got1, tt.want1)
			}
		})
	}
}

type FakeReader struct {
}

func (*FakeReader) Config() *params.ChainConfig {
	panic("implement me")
}

func (*FakeReader) CurrentHeader() *types.Header {
	panic("implement me")
}

func (*FakeReader) GetHeader(hash common.Hash, number uint64) *types.Header {
	panic("implement me")
}

func (*FakeReader) GetHeaderByNumber(number uint64) *types.Header {
	return &types.Header{Number: big.NewInt(0), Time: big.NewInt(0).Sub(big.NewInt(time.Now().Unix()), big.NewInt(100))}
}

func (*FakeReader) GetHeaderByHash(hash common.Hash) *types.Header {
	panic("implement me")
}

func (*FakeReader) GetBlock(hash common.Hash, number uint64) *types.Block {
	panic("implement me")
}

func TestDpor_snapshot(t *testing.T) {
	hash := common.HexToHash("c0")
	cache, _ := lru.NewARC(10)
	snapshotCache, _ := lru.NewARC(10)
	snapshotCache.Add(hash, &Snapshot{})
	config := &params.DporConfig{Epoch: 3}

	type fields struct {
		config       *params.DporConfig
		db           ethdb.Database
		recents      *lru.ARCCache
		signatures   *lru.ARCCache
		signedBlocks map[uint64]common.Hash
		signer       common.Address
		signFn       SignerFn
		lock         sync.RWMutex
	}
	type args struct {
		chain   consensus.ChainReader
		number  uint64
		hash    common.Hash
		parents []*types.Header
	}

	tests := []struct {
		name    string
		fields  fields
		args    args
		want    *Snapshot
		wantErr bool
	}{
		// TODO: Add test cases.
		{"when VerifyHeader failed,return error",
			fields{recents: cache, db: &fakeDb{}, config: config}, args{
			chain: &FakeReader{}, number: 0, hash: common.Hash{},
		}, nil, true},

		{"snapshot cached in recents,return cached value",
			fields{recents: snapshotCache, db: &fakeDb{}, config: config}, args{
			chain: &FakeReader{}, number: 0, hash: hash,
		}, &Snapshot{}, false},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				config:       tt.fields.config,
				db:           tt.fields.db,
				recents:      tt.fields.recents,
				signatures:   tt.fields.signatures,
				signedBlocks: tt.fields.signedBlocks,
				signer:       tt.fields.signer,
				signFn:       tt.fields.signFn,
				lock:         tt.fields.lock,
			}
			got, err := c.snapshot(tt.args.chain, tt.args.number, tt.args.hash, tt.args.parents)
			if (err != nil) != tt.wantErr {
				t.Errorf("Dpor.snapshot(%v, %v, %v, %v) error = %v, wantErr %v", tt.args.chain, tt.args.number, tt.args.hash, tt.args.parents, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("Dpor.snapshot(%v, %v, %v, %v) = %v, want %v", tt.args.chain, tt.args.number, tt.args.hash, tt.args.parents, got, tt.want)
			}
		})
	}
}
func newHeader() *types.Header {
	return &types.Header{
		ParentHash:  common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		UncleHash:   common.HexToHash("0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"),
		Coinbase:    common.HexToAddress("0x8888f1F195AFa192CfeE860698584c030f4c9dB1"),
		Root:        common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxHash:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptHash: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Difficulty:  big.NewInt(131072),
		Number:      big.NewInt(1),
		GasLimit:    uint64(3141592),
		GasUsed:     uint64(21000),
		Time:        big.NewInt(1426516743),
		Extra:       []byte("0x0000000000000000000000000000000000000000000000000000000000000000095e7baea6a6c7c4c2dfeb977efac326af552d87e94b7b6c5a0e526a4d97f9768ad6097bde25c62ac05302acebd0730e3a18a058d7d1cb1204c4a092ef3dd127de235f15ffb4fc0d71469d1339df64650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"),
		//Extra2:      []byte("ext2"),
		MixDigest: common.HexToHash("bd4472abb6659ebe3ee06ee4d7b72a00a9f4d001caca51342001075469aff498"),
		Nonce:     types.EncodeNonce(uint64(0xa13a5a8c8f2bb1c4)),
	}
}

func TestDpor_VerifyUncles(t *testing.T) {
	c := &Dpor{}
	tx1 := types.NewTransaction(0, address, big.NewInt(10), 50000, big.NewInt(10), nil)
	var trans []*types.Transaction = make([]*types.Transaction, 1)
	trans[0] = tx1

	tests := []struct {
		name    string
		uncls   []*types.Header
		wantErr bool
	}{
		{"exist uncles should be error", []*types.Header{newHeader()}, true},
		{"no uncles should be no error", []*types.Header{}, false},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			newBlock := types.NewBlock(newHeader(), trans, test.uncls, nil)
			if err := c.VerifyUncles(nil, newBlock); (err != nil) != test.wantErr {
				t.Errorf("Dpor.VerifyUncles(%v, %v) error = %v, wantErr %v", nil, test.uncls, err, test.wantErr)
			}
		})
	}
}

func TestDpor_VerifySeal(t *testing.T) {
	type fields struct {
		config       *params.DporConfig
		db           ethdb.Database
		recents      *lru.ARCCache
		signatures   *lru.ARCCache
		signedBlocks map[uint64]common.Hash
		signer       common.Address
		signFn       SignerFn
		lock         sync.RWMutex
	}
	type args struct {
		chain     consensus.ChainReader
		header    *types.Header
		refHeader *types.Header
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				config:       tt.fields.config,
				db:           tt.fields.db,
				recents:      tt.fields.recents,
				signatures:   tt.fields.signatures,
				signedBlocks: tt.fields.signedBlocks,
				signer:       tt.fields.signer,
				signFn:       tt.fields.signFn,
				lock:         tt.fields.lock,
			}
			if err := c.VerifySeal(tt.args.chain, tt.args.header, tt.args.refHeader); (err != nil) != tt.wantErr {
				t.Errorf("Dpor.VerifySeal(%v, %v, %v) error = %v, wantErr %v", tt.args.chain, tt.args.header, tt.args.refHeader, err, tt.wantErr)
			}
		})
	}
}

func Test_acceptSigs(t *testing.T) {
	header := &types.Header{
		Coinbase:    addr1,
		Number:      big.NewInt(1),
		Difficulty:  big.NewInt(int64(1)),
		UncleHash:   types.EmptyUncleHash,
		TxHash:      types.EmptyRootHash,
		ReceiptHash: types.EmptyRootHash,
	}
	sigs := make(map[common.Address][]byte)
	for _, signer := range getSignerAddress() {
		sigs[signer] = []byte("ok")
	}
	cache, _ := lru.NewARC(inmemorySnapshots)
	cache.Add(header.Hash(), sigs)

	type args struct {
		header   *types.Header
		sigcache *lru.ARCCache
		signers  []common.Address
	}
	tests := []struct {
		name    string
		args    args
		want    bool
		wantErr bool
	}{
		{"should be true when signer not in cache", args{header, cache, getSignerAddress()[1:2]}, false, false},
		{"should be true when signer in cache", args{header, cache, getSignerAddress()}, true, false},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := acceptSigs(tt.args.header, tt.args.sigcache, tt.args.signers)
			if (err != nil) != tt.wantErr {
				t.Errorf("acceptSigs(%v, %v, %v) error = %v, wantErr %v", tt.args.header, tt.args.sigcache, tt.args.signers, err, tt.wantErr)
				return
			}
			if got != tt.want {
				t.Errorf("acceptSigs(%v, %v, %v) = %v, want %v", tt.args.header, tt.args.sigcache, tt.args.signers, got, tt.want)
			}
		})
	}
}

func TestDpor_Prepare(t *testing.T) {
	type fields struct {
		config       *params.DporConfig
		db           ethdb.Database
		recents      *lru.ARCCache
		signatures   *lru.ARCCache
		signedBlocks map[uint64]common.Hash
		signer       common.Address
		signFn       SignerFn
		lock         sync.RWMutex
	}
	type args struct {
		chain  consensus.ChainReader
		header *types.Header
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				config:       tt.fields.config,
				db:           tt.fields.db,
				recents:      tt.fields.recents,
				signatures:   tt.fields.signatures,
				signedBlocks: tt.fields.signedBlocks,
				signer:       tt.fields.signer,
				signFn:       tt.fields.signFn,
				lock:         tt.fields.lock,
			}
			if err := c.Prepare(tt.args.chain, tt.args.header); (err != nil) != tt.wantErr {
				t.Errorf("Dpor.Prepare(%v, %v) error = %v, wantErr %v", tt.args.chain, tt.args.header, err, tt.wantErr)
			}
		})
	}
}

func TestDpor_Finalize(t *testing.T) {
	type fields struct {
		config       *params.DporConfig
		db           ethdb.Database
		recents      *lru.ARCCache
		signatures   *lru.ARCCache
		signedBlocks map[uint64]common.Hash
		signer       common.Address
		signFn       SignerFn
		lock         sync.RWMutex
	}
	type args struct {
		chain    consensus.ChainReader
		header   *types.Header
		state    *state.StateDB
		txs      []*types.Transaction
		uncles   []*types.Header
		receipts []*types.Receipt
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		want    *types.Block
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				config:       tt.fields.config,
				db:           tt.fields.db,
				recents:      tt.fields.recents,
				signatures:   tt.fields.signatures,
				signedBlocks: tt.fields.signedBlocks,
				signer:       tt.fields.signer,
				signFn:       tt.fields.signFn,
				lock:         tt.fields.lock,
			}
			got, err := c.Finalize(tt.args.chain, tt.args.header, tt.args.state, tt.args.txs, tt.args.uncles, tt.args.receipts)
			if (err != nil) != tt.wantErr {
				t.Errorf("Dpor.Finalize(%v, %v, %v, %v, %v, %v) error = %v, wantErr %v", tt.args.chain, tt.args.header, tt.args.state, tt.args.txs, tt.args.uncles, tt.args.receipts, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("Dpor.Finalize(%v, %v, %v, %v, %v, %v) = %v, want %v", tt.args.chain, tt.args.header, tt.args.state, tt.args.txs, tt.args.uncles, tt.args.receipts, got, tt.want)
			}
		})
	}
}

func TestDpor_Authorize(t *testing.T) {
	type fields struct {
		config       *params.DporConfig
		db           ethdb.Database
		recents      *lru.ARCCache
		signatures   *lru.ARCCache
		signedBlocks map[uint64]common.Hash
		signer       common.Address
		signFn       SignerFn
		lock         sync.RWMutex
	}
	type args struct {
		signer common.Address
		signFn SignerFn
	}
	tests := []struct {
		name   string
		fields fields
		args   args
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				config:       tt.fields.config,
				db:           tt.fields.db,
				recents:      tt.fields.recents,
				signatures:   tt.fields.signatures,
				signedBlocks: tt.fields.signedBlocks,
				signer:       tt.fields.signer,
				signFn:       tt.fields.signFn,
				lock:         tt.fields.lock,
			}
			c.Authorize(tt.args.signer, tt.args.signFn)
		})
	}
}

func TestDpor_Seal(t *testing.T) {
	type fields struct {
		config       *params.DporConfig
		db           ethdb.Database
		recents      *lru.ARCCache
		signatures   *lru.ARCCache
		signedBlocks map[uint64]common.Hash
		signer       common.Address
		signFn       SignerFn
		lock         sync.RWMutex
	}
	type args struct {
		chain consensus.ChainReader
		block *types.Block
		stop  <-chan struct{}
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		want    *types.Block
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				config:       tt.fields.config,
				db:           tt.fields.db,
				recents:      tt.fields.recents,
				signatures:   tt.fields.signatures,
				signedBlocks: tt.fields.signedBlocks,
				signer:       tt.fields.signer,
				signFn:       tt.fields.signFn,
				lock:         tt.fields.lock,
			}
			got, err := c.Seal(tt.args.chain, tt.args.block, tt.args.stop)
			if (err != nil) != tt.wantErr {
				t.Errorf("Dpor.Seal(%v, %v, %v) error = %v, wantErr %v", tt.args.chain, tt.args.block, tt.args.stop, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("Dpor.Seal(%v, %v, %v) = %v, want %v", tt.args.chain, tt.args.block, tt.args.stop, got, tt.want)
			}
		})
	}
}

func TestDpor_CalcDifficulty(t *testing.T) {
	type fields struct {
		config       *params.DporConfig
		db           ethdb.Database
		recents      *lru.ARCCache
		signatures   *lru.ARCCache
		signedBlocks map[uint64]common.Hash
		signer       common.Address
		signFn       SignerFn
		lock         sync.RWMutex
	}
	type args struct {
		chain  consensus.ChainReader
		time   uint64
		parent *types.Header
	}
	tests := []struct {
		name   string
		fields fields
		args   args
		want   *big.Int
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				config:       tt.fields.config,
				db:           tt.fields.db,
				recents:      tt.fields.recents,
				signatures:   tt.fields.signatures,
				signedBlocks: tt.fields.signedBlocks,
				signer:       tt.fields.signer,
				signFn:       tt.fields.signFn,
				lock:         tt.fields.lock,
			}
			if got := c.CalcDifficulty(tt.args.chain, tt.args.time, tt.args.parent); !reflect.DeepEqual(got, tt.want) {
				t.Errorf("Dpor.CalcDifficulty(%v, %v, %v) = %v, want %v", tt.args.chain, tt.args.time, tt.args.parent, got, tt.want)
			}
		})
	}
}

func TestCalcDifficulty(t *testing.T) {
	signers := getSignerAddress()
	config := &params.DporConfig{Period: 3, Epoch: 3}
	cache, _ := lru.NewARC(inmemorySnapshots)
	snapshot := newSnapshot(config, cache, 1, common.Hash{}, signers)

	type args struct {
		snap   *Snapshot
		signer common.Address
	}
	tests := []struct {
		name string
		args args
		want *big.Int
	}{
		{name: "WhenSnapshotIsNotLeader", args: args{snapshot, signers[0]}, want: big.NewInt(1)},
		{name: "WhenSnapshotIsLeader", args: args{snapshot, signers[1]}, want: big.NewInt(2)},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := CalcDifficulty(tt.args.snap, tt.args.signer); !reflect.DeepEqual(got, tt.want) {
				t.Errorf("CalcDifficulty(%v, %v) = %v, want %v", tt.args.snap, tt.args.signer, got, tt.want)
			}
		})
	}
}
