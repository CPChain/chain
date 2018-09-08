package types

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
