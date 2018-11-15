// Copyright 2018 The cpchain authors

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
