package types

import (
	"math/big"

	"github.com/ethereum/go-ethereum/common"
)

// PrivateMessage represents the message about private tx, extending normal Message
type PrivateMessage struct {
	Message
	isPrivate bool
}

// NewPrivateMessage creates a new PrivateMessage instance with given parameters.
func NewPrivateMessage(from common.Address, to *common.Address, nonce uint64, amount *big.Int, gasLimit uint64, price *big.Int, data []byte, checkNonce bool, isPrivate bool) PrivateMessage {
	return PrivateMessage{
		Message:   NewMessage(from, to, nonce, amount, gasLimit, price, data, checkNonce),
		isPrivate: isPrivate,
	}
}

// IsPrivate returns if the PrivateMessage instance is private.
func (cm PrivateMessage) IsPrivate() bool {
	return cm.isPrivate
}

// Ref: https://bitcoin.stackexchange.com/questions/38351/ecdsa-v-r-s-what-is-v
const PrivateTxTag1 = 47 // When r is even
const PrivateTxTag2 = 48 // When r is odd

// PrivateTransaction represents a private transaction.
type PrivateTransaction struct {
	*Transaction
}

// AsMessage returns the transaction as a PrivateMessage.
func (tx *PrivateTransaction) ASMessage(s Signer) (PrivateMessage, error) {
	msg, err := tx.Transaction.AsMessage(s)
	if err != nil {
		return PrivateMessage{}, err
	}

	return PrivateMessage{
		Message: msg,
	}, nil
}

// IsPrivate checks if the tx is private.
func (tx *PrivateTransaction) IsPrivate() bool {
	return tx.GetV() == PrivateTxTag1 || tx.GetV() == PrivateTxTag2
}

// SetPrivate sets the tx as private.
func (tx *PrivateTransaction) SetPrivate(isPrivate bool) {
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
