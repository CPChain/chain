package types

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
)

func TestTxIsPrivate(t *testing.T) {
	trans := NewTransaction(0, common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579268"), new(big.Int), 0, new(big.Int), nil)
	prvTrans := PrivateTransaction{trans}

	if prvTrans.IsPrivate() {
		t.Fatal("Initial IsPrivate state should be false.")
	}

	prvTrans.SetPrivate(true)
	if !prvTrans.IsPrivate() {
		t.Fatal("The IsPrivate state should be true.")
	}

	prvTrans.SetPrivate(false)
	if prvTrans.IsPrivate() {
		t.Fatal("The IsPrivate state should be false.")
	}
}

func TestNewCpcMessage(t *testing.T) {
	to := common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579299")
	prvMsg := NewPrivateMessage(common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579268"), &to, 0, new(big.Int), 0, new(big.Int), []byte{}, true, true)
	if !prvMsg.IsPrivate() {
		t.Fatal("The PrivateMessage's IsPrivate state should be set to true.")
	}

	prvMsg = NewPrivateMessage(common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579268"), &to, 0, new(big.Int), 0, new(big.Int), []byte{}, true, false)
	if prvMsg.IsPrivate() {
		t.Fatal("The PrivateMessage's IsPrivate state should be set to false.")
	}
}
