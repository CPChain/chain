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

// PrivateTransaction represents a private transaction.
type PrivateTransaction Transaction

// IsPrivate checks if the tx is private.
func (tx *PrivateTransaction) IsPrivate() bool {
	return tx.data.IsPrivate
}

// SetPrivate sets the tx as private.
func (tx *PrivateTransaction) SetPrivate(isPrivate bool) {
	tx.data.IsPrivate = isPrivate
}
