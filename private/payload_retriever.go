package private

import (
	"crypto/aes"
	"crypto/cipher"
	"encoding/binary"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/database"
	"github.com/ethereum/go-ethereum/rlp"
)

// Read tx's payload replacement, retrieve encrypted payload from IPFS and decrypt it.
// Return decrypted payload, a flag indicating if the node has enough permission and error if there is.
func RetrieveAndDecryptPayload(data []byte, txNonce uint64, remoteDB database.RemoteDatabase, abDecryptor accounts.AccountBasedDecryptor) (payload []byte, hasPermission bool, error error) {
	replacement := PayloadReplacement{}
	err := rlp.DecodeBytes(data, &replacement)
	if err != nil {
		return []byte{}, false, err
	}

	// Check if the current node is in the participant group by comparing is public key and decrypt with its private
	// key and return result.
	sealed, err := getDataFromRemote(replacement.TxPayloadUri, remoteDB)
	if err != nil {
		return []byte{}, false, err
	}

	sp := SealedPrivatePayload{}
	err = rlp.DecodeBytes(sealed, &sp)
	if err != nil {
		return []byte{}, false, err
	}
	for i, k := range replacement.Participants {
		canDecrypt, wallet, acc := abDecryptor.CanDecrypt(k)
		if canDecrypt {
			encryptedKey := sp.SymmetricKeys[i]
			symKey, _ := abDecryptor.Decrypt(encryptedKey, wallet, acc)
			decrypted, _ := decryptPayload(sp.Payload, symKey, txNonce)
			return decrypted, true, nil
		}
	}

	return []byte{}, false, nil
}

func getDataFromRemote(ipfsAddress []byte, remoteDB database.RemoteDatabase) ([]byte, error) {
	content, err := remoteDB.Get(ipfsAddress)
	if err != nil {
		return []byte{}, err
	}
	return content, nil
}

// Decrypt payload with the given symmetric key.
// Returns decrypted payload and error if exists.
func decryptPayload(cipherdata []byte, skey []byte, txNonce uint64) ([]byte, error) {
	// use tx's nonce as gcm nonce
	nonce := make([]byte, 12)
	binary.BigEndian.PutUint64(nonce, txNonce)
	binary.BigEndian.PutUint32(nonce[8:], uint32(txNonce))

	block, err := aes.NewCipher(skey)
	if err != nil {
		return []byte{}, err
	}

	aesgcm, err := cipher.NewGCM(block)
	data, err := aesgcm.Open(nil, nonce, cipherdata, nil)
	if err != nil {
		return []byte{}, err
	}
	return data, nil
}
