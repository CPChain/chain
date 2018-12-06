// Copyright 2018 The cpchain authors

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
