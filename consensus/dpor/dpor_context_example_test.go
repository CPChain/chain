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

package dpor

import (
	"bytes"
	"fmt"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
)

var (
	address = common.HexToAddress("0x00Ce0d46d924CC8437c806721496599FC3FFA268")
)

func ExampleDporContext_encode() {

	var context *DporContext // context is nil pointer to DporContext
	bytes, _ := rlp.EncodeToBytes(context)
	fmt.Printf("%v → %X\n", context, bytes)

	context = &DporContext{
		Name:       "hello",
		Committees: []common.Address{address},
		SignatureInfo: BlockSignatureInfo{
			BlockNumber: 1000,
			BlockSignatures: []BlockSignature{
				{Address: address, Signature: "sign_xxx"}},
		},
		CandidateList: []common.Address{address}}
	bytes, _ = rlp.EncodeToBytes(context)
	fmt.Printf("%v → %X\n", context, bytes)
	//&{hello [[0 206 13 70 217 36 204 132 55 200 6 114 20 150 89 159 195 255 162 104]] {1000 [{[0 206 13 70 217 36 204 132 55 200 6 114 20 150 89 159 195 255 162 104] sign_xxx}]} 0xc42000a420} → F8568568656C6C6FD59400CE0D46D924CC8437C806721496599FC3FFA268E38203E8DFDE9400CE0D46D924CC8437C806721496599FC3FFA268887369676E5F787878D59400CE0D46D924CC8437C806721496599FC3FFA268

	// Output:
	// <nil> → C680C0C280C0C0
	// &{hello [[0 206 13 70 217 36 204 132 55 200 6 114 20 150 89 159 195 255 162 104]] {1000 [{[0 206 13 70 217 36 204 132 55 200 6 114 20 150 89 159 195 255 162 104] sign_xxx}]} [[0 206 13 70 217 36 204 132 55 200 6 114 20 150 89 159 195 255 162 104]]} → F8568568656C6C6FD59400CE0D46D924CC8437C806721496599FC3FFA268E38203E8DFDE9400CE0D46D924CC8437C806721496599FC3FFA268887369676E5F787878D59400CE0D46D924CC8437C806721496599FC3FFA268
}

// rlp/decode_test.go#BenchmarkDecodeIntSliceReuse
func ExampleDporContext_decode() {
	var c DporContext
	if err := rlp.Decode(bytes.NewReader(common.FromHex("F8568568656C6C6FD59400CE0D46D924CC8437C806721496599FC3FFA268E38203E8DFDE9400CE0D46D924CC8437C806721496599FC3FFA268887369676E5F787878D59400CE0D46D924CC8437C806721496599FC3FFA268")), &c); err != nil {
		fmt.Printf("Error: %v\n", err)
	}

	fmt.Printf("Decoded value: %#v\n", c.Name)
	fmt.Printf("BlockNumber value: %d\n", c.SignatureInfo.BlockNumber)
	fmt.Printf("BlockSignatures value: %+v\n", c.SignatureInfo.BlockSignatures)
	fmt.Printf("BlockSignatures.Address value: %+v\n", c.SignatureInfo.BlockSignatures[0].Address.Hex())
	fmt.Printf("BlockSignatures.Signature value: %+v\n", c.SignatureInfo.BlockSignatures[0].Signature)
	fmt.Printf("BlockSignatures.CandidateList value: %+v\n", (c.CandidateList)[0])

	// Output:
	// Decoded value: "hello"
	// BlockNumber value: 1000
	// BlockSignatures value: [{Address:[0 206 13 70 217 36 204 132 55 200 6 114 20 150 89 159 195 255 162 104] Signature:sign_xxx}]
	// BlockSignatures.Address value: 0x00Ce0d46d924CC8437c806721496599FC3FFA268
	// BlockSignatures.Signature value: sign_xxx
	// BlockSignatures.CandidateList value: [0 206 13 70 217 36 204 132 55 200 6 114 20 150 89 159 195 255 162 104]
}
