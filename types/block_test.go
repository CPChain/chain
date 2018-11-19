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

package types

import (
	"bytes"
	"fmt"
	"math/big"
	"reflect"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/stretchr/testify/assert"
)

// from bcValidBlockTest.json, "SimpleTx"
func TestBlockEncoding(t *testing.T) {
	blockEnc := common.FromHex("f90241f901d9a083cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55948888f1f195afa192cfee860698584c030f4c9db1a0ef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017a05fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67a0bc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52b90100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008302000001832fefd8825208845506eb078080a0bd4472abb6659ebe3ee06ee4d7b72a00a9f4d001caca51342001075469aff49888a13a5a8c8f2bb1c4f863f86180800a82c35094095e7baea6a6c7c4c2dfeb977efac326af552d870a80801ba09bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094fa08a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b1")
	var block Block
	if err := rlp.DecodeBytes(blockEnc, &block); err != nil {
		t.Fatal("decode error: ", err)
	}

	check := func(f string, got, want interface{}) {
		if !reflect.DeepEqual(got, want) {
			t.Errorf("%s mismatch: got %v, want %v", f, got, want)
		}
	}
	check("Difficulty", block.Difficulty(), big.NewInt(131072))
	check("GasLimit", block.GasLimit(), uint64(3141592))
	check("GasUsed", block.GasUsed(), uint64(21000))
	check("Coinbase", block.Coinbase(), common.HexToAddress("8888f1f195afa192cfee860698584c030f4c9db1"))
	check("MixHash", block.MixHash(), common.HexToHash("bd4472abb6659ebe3ee06ee4d7b72a00a9f4d001caca51342001075469aff498"))
	check("StateRoot", block.StateRoot(), common.HexToHash("ef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"))
	check("Hash", block.Hash(), common.HexToHash("c8f62a7d2c95731be5fc395f2fa425a248c84ed58e497cc2de8c35495c758d2a"))
	check("Nonce", block.Nonce(), uint64(0xa13a5a8c8f2bb1c4))
	check("Time", block.Time(), big.NewInt(1426516743))
	check("Size", block.Size(), common.StorageSize(len(blockEnc)))

	tx1 := NewTransaction(0, common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"), big.NewInt(10), 50000, big.NewInt(10), nil)

	tx1, _ = tx1.WithSignature(HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))
	fmt.Println(block.Transactions()[0].Hash())
	fmt.Println(tx1.data)
	fmt.Println(tx1.Hash())
	check("len(Transactions)", len(block.Transactions()), 1)
	check("Transactions[0].Hash", block.Transactions()[0].Hash(), tx1.Hash())

	ourBlockEnc, err := rlp.EncodeToBytes(&block)
	if err != nil {
		t.Fatal("encode error: ", err)
	}
	if !bytes.Equal(ourBlockEnc, blockEnc) {
		t.Errorf("encoded block mismatch:\ngot:  %x\nwant: %x", ourBlockEnc, blockEnc)
	}
}

func TestBlockEncodingBuildHex(t *testing.T) {

	tx1 := NewTransaction(0, common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"), big.NewInt(10), 50000, big.NewInt(10), nil)

	tx1, _ = tx1.WithSignature(HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))

	newHeader := &Header{
		ParentHash:   common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		Coinbase:     common.HexToAddress("0x8888f1F195AFa192CfeE860698584c030f4c9dB1"),
		StateRoot:    common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxsRoot:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptsRoot: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Difficulty:   big.NewInt(131072),
		Number:       big.NewInt(1),
		GasLimit:     uint64(3141592),
		GasUsed:      uint64(21000),
		Time:         big.NewInt(1426516743),
		//Extra:       []byte("ext1"),
		//Extra2:      []byte("ext2"),
		MixHash: common.HexToHash("bd4472abb6659ebe3ee06ee4d7b72a00a9f4d001caca51342001075469aff498"),
		Nonce:   EncodeNonce(uint64(0xa13a5a8c8f2bb1c4)),
	}

	newBlock := NewBlockWithHeader(newHeader)
	var xx1 []*Transaction = make([]*Transaction, 1)
	xx1[0] = tx1
	newBlock.transactions = xx1

	var uncls []*Header
	rlp.DecodeBytes(common.Hex2Bytes("c0"), uncls)

	bb, _ := rlp.EncodeToBytes(newBlock)
	hex := common.Bytes2Hex(bb)

	expected := "f90241f901d9a083cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55948888f1f195afa192cfee860698584c030f4c9db1a0ef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017a05fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67a0bc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52b90100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008302000001832fefd8825208845506eb078080a0bd4472abb6659ebe3ee06ee4d7b72a00a9f4d001caca51342001075469aff49888a13a5a8c8f2bb1c4f863f86180800a82c35094095e7baea6a6c7c4c2dfeb977efac326af552d870a80801ba09bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094fa08a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b1"
	assert.Equal(t, expected, hex)
}

var (
	addr1 = common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465")
	addr2 = common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092")
	addr3 = common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")
	addr4 = common.HexToAddress("0x3333333333333333333333333333333333333333")
	seal  = common.Hex2Bytes("123598ab34ae034858899923bc333000000043432215abb12dc0000000000000000000000000000000000000000000000000000000000000000000000000010101")
	sig1  = common.Hex2Bytes("000000000123598ab34ae034858899923bc33000000000000000000000000003000000043432215abb12dc0000000000000000000000000000000000000222222a")
	sig2  = common.Hex2Bytes("00000dc000000000000000000000123598ab34ae034858899923bc330000334554322aa000000000003000000043432215abb1200000000000000000000222222a")
)

func TestBlockHeaderGetDpor(t *testing.T) {
	newHeader := &Header{}
	newHeader.Extra = append(append(append(common.Hex2Bytes("0000000000000000000000000000000000000000000000000000000000000000"),
		addr1[:]...), addr2[:]...), seal...)
	newHeader.Extra2 = append(sig1, sig2...)
	dpor := newHeader.GetDpor()
	if len(dpor.Proposers) != 2 {
		t.Errorf("number of proposers is wrong, want 2, but got %d", len(dpor.Proposers))
	}

	if !reflect.DeepEqual(dpor.Proposers[0], addr1) || !reflect.DeepEqual(dpor.Proposers[1], addr2) {
		t.Error("The proposers are wrong")
	}
	if !reflect.DeepEqual(dpor.Seal[:], seal) {
		t.Error("The seal is wrong")
	}

	if !reflect.DeepEqual(dpor.Sigs[0][:], sig1) || !reflect.DeepEqual(dpor.Sigs[1][:], sig2) {
		t.Error("The validator signatures are wrong")
	}
}

func TestBlockHeaderSaveDpor(t *testing.T) {
	// Prepare a header with defined dpor field
	newHeader := &Header{}
	copy(newHeader.Dpor.Seal[:], seal)
	newHeader.Dpor.Sigs = make([]DporSignature, 2)
	copy(newHeader.Dpor.Sigs[0][:], sig1)
	copy(newHeader.Dpor.Sigs[1][:], sig2)
	newHeader.Dpor.Proposers = make([]common.Address, 2)
	copy(newHeader.Dpor.Proposers[0][:], addr1[:])
	copy(newHeader.Dpor.Proposers[1][:], addr2[:])
	newHeader.Extra = bytes.Repeat([]byte{0x00}, extraVanity)

	// save dpor filed to extra and extra2
	newHeader.SaveDporSnapToExtras()

	expectedExtra := append(append(append(bytes.Repeat([]byte{0x00}, extraVanity), addr1[:]...), addr2[:]...), seal[:]...)
	if !reflect.DeepEqual(newHeader.Extra, expectedExtra) {
		t.Error("the extra is not as expected")
	}

	expectedExtra2 := append(sig1, sig2[:]...)
	if !reflect.DeepEqual(newHeader.Extra2, expectedExtra2) {
		t.Error("the extra2 is not as expected")
	}
}
