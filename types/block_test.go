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
	"encoding/json"
	"fmt"
	"math/big"
	"reflect"
	"strings"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/stretchr/testify/assert"
)

// from bcValidBlockTest.json, "SimpleTx"
func TestBlockEncoding(t *testing.T) {
	blockEnc := common.FromHex("f90259f901f2a083cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55948888f1f195afa192cfee860698584c030f4c9db1a0ef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017a05fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67a0bc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52b901000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001832fefd8825208845506eb0780f846b8410000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c0c0f862f86080800a82c35094095e7baea6a6c7c4c2dfeb977efac326af552d870a801ba09bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094fa08a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b1")

	var block Block
	if err := rlp.DecodeBytes(blockEnc, &block); err != nil {
		t.Fatal("decode error: ", err)
	}

	check := func(f string, got, want interface{}) {
		if !reflect.DeepEqual(got, want) {
			t.Errorf("%s mismatch: got %v, want %v", f, got, want)
		}
	}
	check("GasLimit", block.GasLimit(), uint64(3141592))
	check("GasUsed", block.GasUsed(), uint64(21000))
	check("Coinbase", strings.ToLower(block.Coinbase().Hex()), "0x8888f1f195afa192cfee860698584c030f4c9db1")
	check("StateRoot", strings.ToLower(block.StateRoot().Hex()), "0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017")
	check("Hash", block.Hash().Hex(), "0x62334eae00769d9efe592007afeae06044e3625de335dae1a0d276b40d697a14")
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
		TxsRoot:      common.HexToHash("0x5fe50b260da63ø08036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptsRoot: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Number:       big.NewInt(1),
		GasLimit:     uint64(3141592),
		GasUsed:      uint64(21000),
		Time:         big.NewInt(1426516743),
	}

	newBlock := NewBlockWithHeader(newHeader)
	var xx1 []*Transaction = make([]*Transaction, 1)
	xx1[0] = tx1
	newBlock.transactions = xx1

	bb, _ := rlp.EncodeToBytes(newBlock)
	hex := common.Bytes2Hex(bb)

	expected := "f90259f901f2a083cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55948888f1f195afa192cfee860698584c030f4c9db1a0ef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017a000000000000000000000000000000000000000000000000000005fe50b260da6a0bc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52b901000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001832fefd8825208845506eb0780f846b8410000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c0c0f862f86080800a82c35094095e7baea6a6c7c4c2dfeb977efac326af552d870a801ba09bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094fa08a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b1"
	assert.Equal(t, expected, hex)
}

var (
	addr1 = common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465")
	addr2 = common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092")
	addr3 = common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")
	addr4 = common.HexToAddress("0x3333333333333333333333333333333333333333")
	seal  = HexToDporSig("0x123598ab34ae034858899923bc333000000043432215abb12dc0000000000000000000000000000000000000000000000000000000000000000000000000010101")
	sig1  = HexToDporSig("0x000000000123598ab34ae034858899923bc33000000000000000000000000003000000043432215abb12dc0000000000000000000000000000000000000222222a")
	sig2  = HexToDporSig("0x00000dc000000000000000000000123598ab34ae034858899923bc330000334554322aa000000000003000000043432215abb1200000000000000000000222222a")
)

func TestCopyDporSnap(t *testing.T) {
	newHeader := &Header{}
	newHeader.Extra = append(common.FromHex("0x0000000000000000000000000000000000000000000000000000000000000000"))
	newHeader.Dpor.Proposers = []common.Address{addr1, addr2}
	newHeader.Dpor.Seal = seal
	newHeader.Dpor.Sigs = []DporSignature{sig1, sig2}
	dpor := CopyDporSnap(&newHeader.Dpor)
	if len(dpor.Proposers) != 2 {
		t.Errorf("number of proposers is wrong, want 2, but got %d", len(dpor.Proposers))
	}

	if !reflect.DeepEqual(dpor.Proposers[0], addr1) || !reflect.DeepEqual(dpor.Proposers[1], addr2) {
		t.Error("The proposers are wrong")
	}
	if !reflect.DeepEqual(dpor.Seal, seal) {
		t.Error("The seal is wrong")
	}

	if !reflect.DeepEqual(dpor.Sigs[0], sig1) || !reflect.DeepEqual(dpor.Sigs[1], sig2) {
		t.Error("The validator signatures are wrong")
	}
}

func TestBlockDporRlp(t *testing.T) {
	newHeader := &Header{}
	newHeader.Extra = append(common.FromHex("0x0000000000000000000000000000000000000000000000000000000000000000"))
	newHeader.Dpor.Proposers = []common.Address{addr1, addr2}
	newHeader.Dpor.Seal = seal
	newHeader.Dpor.Sigs = []DporSignature{sig1, sig2}
	dpor := CopyDporSnap(&newHeader.Dpor)

	dp, err := rlp.EncodeToBytes(&dpor)
	// txt, err := dpor.MarshalText()
	if err != nil {
		t.Error("MarshalText error", "error", err)
	}

	fmt.Println("dp", dp)
	ds := DporSnap{}
	err = rlp.DecodeBytes(dp, &ds)
	if err != nil {
		t.Error("UnmarshalText error", "error", err)
	}
	fmt.Println(dp)
}

func TestDporSignatureJsonEncoding(t *testing.T) {
	sig := HexToDporSig("0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00")
	jsonBytes, err := json.Marshal(sig)

	if err != nil {
		t.Error("error:", err)
	}
	fmt.Println("jsonBytes:", string(jsonBytes))

	var ds DporSignature
	err = json.Unmarshal(jsonBytes, &ds)
	if err != nil {
		t.Error("error:", err)
	}
	fmt.Printf("\nunmarshal:%+v\n", ds)
	assert.Equal(t, sig, ds)
}

func TestDporSnapJsonEncoding(t *testing.T) {
	dpor := DporSnap{
		Seal:       seal,
		Sigs:       []DporSignature{sig1, sig2},
		Proposers:  []common.Address{addr1, addr2},
		Validators: []common.Address{addr1, addr2},
	}
	jsonBytes, err := json.Marshal(dpor)
	if err != nil {
		fmt.Println("err:", err)
	}
	string1 := string(jsonBytes)
	fmt.Println("json:", string1)
	fmt.Println("============================================================")

	var dporSnap DporSnap
	err = json.Unmarshal(jsonBytes, &dporSnap)
	if err != nil {
		t.Error("Unmarshal error", "error", err)
	}
	fmt.Println("Seal:", dporSnap.Seal)
	fmt.Println("Sigs:", dporSnap.Sigs)
	fmt.Println("Proposers:", dporSnap.Proposers)
	fmt.Println("Validators:", dporSnap.Validators)
	fmt.Println("============================================================")

	jsonBytes, err = json.Marshal(dporSnap)
	if err != nil {
		fmt.Println("err:", err)
	}
	string2 := string(jsonBytes)
	fmt.Println("new json:", string2)

	assert.Equal(t, string1, string2)
	assert.Equal(t, dpor, dporSnap)

}
