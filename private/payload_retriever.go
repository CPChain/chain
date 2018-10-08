package private

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/rsa"
	"crypto/x509"
	"encoding/binary"

	"bitbucket.org/cpchain/chain/ethdb"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/rlp"
)

// Read tx's payload replacement, retrieve encrypted payload from IPFS and decrypt it.
// Return decrypted payload, a flag indicating if the node has enough permission and error if there is.
func RetrieveAndDecryptPayload(data []byte, txNonce uint64, remoteDB ethdb.RemoteDatabase, pubKey *rsa.PublicKey,
	privKey *rsa.PrivateKey) (payload []byte, hasPermission bool, error error) {
	replacement := PayloadReplacement{}
	err := rlp.DecodeBytes(data, &replacement)
	if err != nil {
		return []byte{}, false, err
	}

	pubEncoded := hexutil.Encode(x509.MarshalPKCS1PublicKey(pubKey))

	// Check if the current node is in the participant group by comparing is public key and decrypt with its private
	// key and return result.
	sealed := getDataFromRemote(replacement.TxPayloadUri, remoteDB)
	sp := SealedPrivatePayload{}
	err = rlp.DecodeBytes(sealed, &sp)
	if err != nil {
		return []byte{}, false, err
	}
	for i, k := range replacement.Participants {
		encryptedKey := sp.SymmetricKeys[i]
		// If the participant's public key equals to current public key, decrypt with corresponding private key.
		if k == pubEncoded {
			symKey := decryptSymKey(encryptedKey, privKey)
			decrypted, _ := decryptPayload(sp.Payload, symKey, txNonce)
			return decrypted, true, nil
		}
	}

	return []byte{}, false, nil
}

func getDataFromRemote(ipfsAddress []byte, remoteDB ethdb.RemoteDatabase) []byte {
	content, err := remoteDB.Get(ipfsAddress)
	if err != nil {
		return []byte{}
	}
	return content
}

func decryptSymKey(data []byte, privateKey *rsa.PrivateKey) []byte {
	decrypted, _ := rsa.DecryptPKCS1v15(nil, privateKey, data)
	return decrypted
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
