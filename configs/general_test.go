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

package configs

import (
	"encoding/json"
	"fmt"
	"testing"

	"github.com/ethereum/go-ethereum/common"
)

func TestDporConfig(t *testing.T) {
	contracts := map[string]common.Address{}
	contracts["t1"] = common.HexToAddress("0x01")
	contracts["t2"] = common.HexToAddress("0x02")
	dc := &DporConfig{Contracts: contracts}
	s, err := json.Marshal(dc)
	if err != nil {
		t.Error("marshal json error")
	}
	fmt.Println("s:", string(s))
}
