package types

import (
	"math/big"
)

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

// GetV returns V value.
func (tx *PrivateTransaction) GetV() uint64 {
	if tx.data.V != nil {
		return tx.data.V.Uint64()
	} else {
		return 0
	}
}

// SetV sets V value by given value.
func (tx *PrivateTransaction) SetV(v uint64) {
	if tx.data.V == nil {
		tx.data.V = &big.Int{}
	}
	tx.data.V.SetUint64(v)
}
