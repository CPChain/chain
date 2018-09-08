package types

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
)

func TestTxIsPrivate(t *testing.T) {
	trans := NewTransaction(0, common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579268"), new(big.Int), 0, new(big.Int), nil)
	privTrans := (*PrivateTransaction)(trans)

	privTrans.SetPrivate(true)
	if !privTrans.IsPrivate() {
		t.Fatal("The IsPrivate state should be true.")
	}

	privTrans.SetPrivate(false)
	if privTrans.IsPrivate() {
		t.Fatal("The IsPrivate state should be false.")
	}
}
