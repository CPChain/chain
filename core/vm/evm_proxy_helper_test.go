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

package vm

import (
	"testing"

	"github.com/ethereum/go-ethereum/common"
)

func TestGetContractInput(t *testing.T) {
	addr := common.HexToAddress("0x7900dd1d71fc5c57ba56e4b768de3c2264253335")
	expected := "8099b6810000000000000000000000007900dd1d71fc5c57ba56e4b768de3c2264253335"
	b1 := getContractInput(addr)
	bh := common.Bytes2Hex(b1)
	if bh != expected {
		t.Errorf("result error expected:%v,got:%v", expected, bh)
	}
}
