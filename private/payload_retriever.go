package private

import (
	"crypto/rsa"
	"crypto/x509"

	"crypto/aes"
	"crypto/cipher"
	"encoding/binary"

	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/rlp"
)

// Read tx's payload replacement, retrieve encrypted payload from IPFS and decrypt it.
// Return decrypted payload, a flag indicating if the node has enough permission and error if there is.
func RetrieveAndDecryptPayload(data []byte, txNonce uint64) (payload []byte, hasPermission bool, err error) {
	prv := getKey()
	pub := hexutil.Encode(x509.MarshalPKCS1PublicKey(&prv.PublicKey))
	replacement := PayloadReplacement{}
	e := rlp.DecodeBytes(data, &replacement)
	if e != nil {
		panic(e)
	}

	// Check if the current node is in the participant group by comapring public key.
	// Decrypt with its private key and return result.
	sealed := getDataFromIpfs(replacement.Address)
	sp := SealedPrivatePayload{}
	e = rlp.DecodeBytes(sealed, &sp)
	if e != nil {
		panic(e)
	}
	for i, k := range replacement.Participants {
		encryptedKey := sp.SymmetricKeys[i]
		// If the participant's public key equals to current public key, decrypt with corresponding private key.
		if k == pub {
			symKey := decryptSymKey(encryptedKey, prv)
			decrypted, e := decryptPayload(sp.Payload, symKey, txNonce)
			return decrypted, true, e
		}
	}

	return []byte{}, false, nil
}

func getDataFromIpfs(ipfsAddress []byte) []byte {
	ipfsDb := ethdb.NewIpfsDb(DefaultIpfsUrl)
	content, err := ipfsDb.Get(ipfsAddress)
	if err != nil {
		panic(err)
	}
	return content
}

func getKey() *rsa.PrivateKey {
	// TODO: replace the hardcoded stuff with real code.
	return GetPrivateKeyForAccount("c05302acebd0730e3a18a058d7d1cb1204c4a092")
}

func decryptSymKey(data []byte, privateKey *rsa.PrivateKey) []byte {
	decrypted, err := rsa.DecryptPKCS1v15(nil, privateKey, data)
	if err != nil {
		panic(err)
	}
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
		return nil, err
	}

	aesgcm, err := cipher.NewGCM(block)
	data, err := aesgcm.Open(nil, nonce, cipherdata, nil)
	if err != nil {
		return nil, err
	}
	return data, nil
}
