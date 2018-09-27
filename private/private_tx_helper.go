package private

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"encoding/binary"
	"io"

	"bitbucket.org/cpchain/chain/common/hexutil"
	"bitbucket.org/cpchain/chain/ethdb"
	"bitbucket.org/cpchain/chain/rlp"
)

// SealedPrivatePayload represents a sealed payload entity in IPFS.
type SealedPrivatePayload struct {
	// Payload represents the encrypted payload with a random symmetric key.
	Payload []byte
	// For public keys, the order is consistent in SymmetricKeys and Participants.
	// SymmetricKeys represents the symmetric key encrypted with participants' public keys. The same symmetric key but encrypted with different RSA public key.
	SymmetricKeys [][]byte
	// Participants represents the public keys of participants.
	Participants [][]byte
}

// NewSealedPrivatePayload creates new SealedPrivatePayload instance with given parameters.
func NewSealedPrivatePayload(encryptedPayload []byte, symmetricKey [][]byte, participants []*rsa.PublicKey) SealedPrivatePayload {
	keysToStore := make([][]byte, len(participants))
	for i, key := range participants {
		keysToStore[i] = x509.MarshalPKCS1PublicKey(key)
	}

	return SealedPrivatePayload{
		Payload:       encryptedPayload,
		SymmetricKeys: symmetricKey,
		Participants:  keysToStore,
	}
}

// toBytes returns serialized SealedPrivatePayload instance represented by bytes.
func (sealed *SealedPrivatePayload) toBytes() ([]byte, error) {
	return rlp.EncodeToBytes(sealed)
}

// PayloadReplacement represents the replacement data which substitute the private tx payload.
type PayloadReplacement struct {
	// Participants represents a list of public keys which belongs to defined participants. They are used for encryption of symmetric key.
	Participants []string
	// TxPayloadUri represents an IPFS address which actually a hash of content.
	TxPayloadUri []byte
}

// SealPrivatePayload encrypts private tx's payload and sends it to IPFS, then replaces the payload with the address in IPFS.
// Returns an address which could be used to retrieve original payload from IPFS.
func SealPrivatePayload(payload []byte, txNonce uint64, participants []string, remoteDB ethdb.RemoteDatabase) (PayloadReplacement, error) {
	// Encrypt payload
	// use tx's nonce as gcm nonce
	nonce := make([]byte, 12)
	binary.BigEndian.PutUint64(nonce, txNonce)
	binary.BigEndian.PutUint32(nonce[8:], uint32(txNonce))
	encryptedPayload, symKey, _ := encryptPayload(payload, nonce)

	pubKeys, _ := stringsToPublicKeys(participants)

	// Encrypt symmetric keys for participants with related public key.
	symKeys := sealSymmetricKey(symKey, pubKeys)

	// Seal the payload by encrypting payload and appending symmetric key and participants.
	sealed := NewSealedPrivatePayload(encryptedPayload, symKeys, pubKeys)

	// Put to IPFS
	bytesToPut, _ := sealed.toBytes()
	ipfsAddr, err := remoteDB.Put(bytesToPut)
	if err != nil {
		return PayloadReplacement{}, err
	}

	// Enclose as a PayloadReplacement struct.
	replacement := PayloadReplacement{
		TxPayloadUri: ipfsAddr,
		Participants: participants,
	}
	return replacement, nil
}

// stringsToPublicKeys converts string to rsa.PublicKey instance.
func stringsToPublicKeys(keys []string) ([]*rsa.PublicKey, error) {
	pubKeys := make([]*rsa.PublicKey, len(keys))

	for i, p := range keys {
		if p[:2] != "0x" {
			p = "0x" + p
		}
		keyBuf, _ := hexutil.Decode(p)
		pubKeys[i], _ = x509.ParsePKCS1PublicKey(keyBuf)
	}
	return pubKeys, nil
}

// sealSymmetricKey sealed symmetric key by encrypting it with participant's public keys one by one.
func sealSymmetricKey(symKey []byte, keys []*rsa.PublicKey) [][]byte {
	result := make([][]byte, len(keys))
	for i, key := range keys {
		encryptedKey, _ := rsa.EncryptPKCS1v15(rand.Reader, key, symKey)
		result[i] = encryptedKey
	}

	return result
}

const keyLength = 32

// generateSymmetricKey generate a random symmetric key.
func generateSymmetricKey() []byte {
	key := make([]byte, keyLength)
	io.ReadFull(rand.Reader, key)
	return key
}

// encryptPayload encrypts payload with a random symmetric key and returns encrypted payload and the random symmetric key.
func encryptPayload(payload []byte, nonce []byte) (encryptedPayload []byte, symmetricKey []byte, err error) {
	symKey := generateSymmetricKey()

	block, _ := aes.NewCipher(symKey)

	aesgcm, _ := cipher.NewGCM(block)

	encrypted := aesgcm.Seal(nil, nonce, payload, nil)
	return encrypted, symKey, nil
}
