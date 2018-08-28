package private

import (
	"math/big"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
)

// Represents the Cpchain message which supports private tx, extending normal Message
type CpcMessage struct {
	types.Message
	isPrivate bool
}

func NewCpcMessage(from common.Address, to *common.Address, nonce uint64, amount *big.Int, gasLimit uint64, price *big.Int, data []byte, checkNonce bool, isPrivate bool) CpcMessage {
	return CpcMessage{
		Message:   types.NewMessage(from, to, nonce, amount, gasLimit, price, data, checkNonce),
		isPrivate: isPrivate,
	}
}

func (cm CpcMessage) IsPrivate() bool {
	return cm.isPrivate
}

// Ref: https://bitcoin.stackexchange.com/questions/38351/ecdsa-v-r-s-what-is-v
const PrivateTxTag1 = 47 // When r is even
const PrivateTxTag2 = 48 // When r is odd

// Represent CPChain transaction
type CpcTransaction struct {
	types.Transaction
}

// AsMessage returns the transaction as a CpcMessage.
func (tx *CpcTransaction) ASMessage(s types.Signer) (CpcMessage, error) {
	msg, err := tx.Transaction.AsMessage(s)
	if err != nil {
		return CpcMessage{}, err
	}

	return CpcMessage{
		Message: msg,
	}, nil
}

// Check if the CPChain tx is private
func (tx *CpcTransaction) IsPrivate() bool {
	return tx.GetV() == PrivateTxTag1 || tx.GetV() == PrivateTxTag2
}

// Set the tx as private
func (tx *CpcTransaction) SetPrivate(isPrivate bool) {
	if isPrivate {
		if tx.GetV() == 28 {
			tx.SetV(PrivateTxTag2)
		} else {
			tx.SetV(PrivateTxTag1)
		}
	} else {
		if tx.GetV() == PrivateTxTag2 {
			tx.SetV(28)
		} else {
			tx.SetV(27)
		}
	}
}
