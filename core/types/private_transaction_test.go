package types

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
)

func TestTxIsPrivate(t *testing.T) {
	trans := NewTransaction(0, common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579268"), new(big.Int), 0, new(big.Int), nil)
	privTrans := (*PrivateTransaction)(trans)

	privTrans.data.V.SetUint64(27)
	if privTrans.IsPrivate() {
		t.Fatal("Initial IsPrivate state should be false.")
	}

	privTrans.SetPrivate(true)
	if !privTrans.IsPrivate() {
		t.Fatal("The IsPrivate state should be true.")
	}

	privTrans.SetPrivate(false)
	if privTrans.IsPrivate() {
		t.Fatal("The IsPrivate state should be false.")
	}

	privTrans.data.V.SetUint64(28)
	if privTrans.IsPrivate() {
		t.Fatal("The IsPrivate state should be false. ")
	}

	privTrans.SetPrivate(true)
	if !privTrans.IsPrivate() {
		t.Fatal("The IsPrivate state should be true. ")
	}

	privTrans.SetPrivate(false)
	if privTrans.data.V.Uint64() != 28 {
		t.Fatal("The V shoudl be restored to 28. ")
	}
}

func TestNewCpcMessage(t *testing.T) {
	to := common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579299")
	cpcMsg := NewPrivateMessage(common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579268"), &to, 0, new(big.Int), 0, new(big.Int), []byte{}, true, true)
	if !cpcMsg.IsPrivate() {
		t.Fatal("The PrivateMessage's IsPrivate state should be set to true.")
	}

	cpcMsg = NewPrivateMessage(common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579268"), &to, 0, new(big.Int), 0, new(big.Int), []byte{}, true, false)
	if cpcMsg.IsPrivate() {
		t.Fatal("The PrivateMessage's IsPrivate state should be set to false.")
	}
}

func TestGetSetV(t *testing.T) {
	trans := NewTransaction(0, common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579268"), new(big.Int), 0, new(big.Int), nil)
	privTrans := (*PrivateTransaction)(trans)
	privTrans.data.V = nil
	if privTrans.GetV() != 0 {
		t.Fatal("The GetV should return 0 when data.V is nil.")
	}

	privTrans.SetV(27)
	if privTrans.GetV() != 27 {
		t.Fatal("The GetV should return 27.")
	}
}
