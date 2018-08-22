package private

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"encoding/binary"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/rlp"
	"io"
)

type SealedPrivatePayload struct {
	Payload      []byte
	SymmetricKey []byte
	Participants []common.Address
}

func NewSealedPrivatePayload(encryptedPayload []byte, symmetricKey []byte, participants []common.Address) SealedPrivatePayload {
	return SealedPrivatePayload{
		Payload:      encryptedPayload,
		SymmetricKey: symmetricKey,
		Participants: participants,
	}
}

func (sealed *SealedPrivatePayload) toBytes() ([]byte, error) {
	bytes, err := rlp.EncodeToBytes(sealed)
	if err != nil {
		panic(err)
	}
	return bytes, nil
}

const defaultDbUrl = "localhost:5001"

// Encrypt private tx's payload and send to IPFS, then replace the payload with the address in IPFS.
// Returns an address which could be used to retrieve original payload from IPFS.
func SealPrivatePayload(payload []byte, txNonce uint64) ([]byte, error) {
	// Encrypt payload
	// use tx's nonce as gcm nonce
	nonce := make([]byte, 12)
	binary.BigEndian.PutUint64(nonce, txNonce)
	binary.BigEndian.PutUint32(nonce[8:], uint32(txNonce))
	encryptPayload, symKey, err := encryptPayload(payload, nonce)
	if err != nil {
		panic(err)
	}

	// Seal the payload by encrypting payload and appending symmetric key and participants.
	sealed := NewSealedPrivatePayload(encryptPayload, symKey, []common.Address{})

	// Put to IPFS
	ipfsDb := ethdb.NewIpfsDb(defaultDbUrl)
	bytesToPut, _ := sealed.toBytes()
	return ipfsDb.Put(bytesToPut)
}

const Key_Length = 32

// Generate a random symmetric key.
func generateSymmetricKey() ([]byte, error) {
	key := make([]byte, Key_Length)
	if _, err := io.ReadFull(rand.Reader, key); err != nil {
		return nil, err
	}
	return key, nil
}

// Encrypt payload with a random symmetric key.
// Returns encrypted payload and the random symmetric key.
func encryptPayload(payload []byte, nonce []byte) (encryptedPayload []byte, symmetricKey []byte, err error) {
	symKey, err := generateSymmetricKey()
	if err != nil {
		panic(err)
	}

	block, err := aes.NewCipher(symKey)
	if err != nil {
		panic(err)
	}

	aesgcm, err := cipher.NewGCM(block)
	if err != nil {
		panic(err)
	}

	encrypted := aesgcm.Seal(nil, nonce, payload, nil)
	return encrypted, symKey, nil
}

// Decrypt payload with the given symmetric key.
// Returns decrypted payload and error if exists.
func decrypt(cipherdata []byte, skey []byte, nonce []byte) ([]byte, error) {
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
