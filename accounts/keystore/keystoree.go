package keystore

import (
	"github.com/ethereum/go-ethereum/accounts"
)

// GetDecryptedKey sucks.
func (ks *KeyStore) GetDecryptedKey(a accounts.Account, passphrase string) (accounts.Account, *Key, error) {
	a, key, err := ks.getDecryptedKey(a, passphrase)
	return a, key, err
}
