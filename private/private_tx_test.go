package private

import (
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
)

func TestTxIsPrivate(t *testing.T) {
	trans := types.NewTransaction(0, common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579268"), new(big.Int), 0, new(big.Int), nil)
	cpcTrans := CpcTransaction{*trans}

	if cpcTrans.IsPrivate() {
		t.Fatal("Initial IsPrivate state should be false.")
	}

	cpcTrans.SetPrivate(true)
	if !cpcTrans.IsPrivate() {
		t.Fatal("The IsPrivate state should be true.")
	}

	cpcTrans.SetPrivate(false)
	if cpcTrans.IsPrivate() {
		t.Fatal("The IsPrivate state should be false.")
	}
}

func TestNewCpcMessage(t *testing.T) {
	to := common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579299")
	cpcMsg := NewCpcMessage(common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579268"), &to, 0, new(big.Int), 0, new(big.Int), []byte{}, true, true)
	if !cpcMsg.IsPrivate() {
		t.Fatal("The CpcMessage's IsPrivate state should be set to true.")
	}

	cpcMsg = NewCpcMessage(common.HexToAddress("0xb794f5ea0ba39494ce83a213fffba74279579268"), &to, 0, new(big.Int), 0, new(big.Int), []byte{}, true, false)
	if cpcMsg.IsPrivate() {
		t.Fatal("The CpcMessage's IsPrivate state should be set to false.")
	}
}
