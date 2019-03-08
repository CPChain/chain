// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package private

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"encoding/binary"
	"io"

	"crypto/ecdsa"

	"bitbucket.org/cpchain/chain/commons/crypto/ecieskey"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/database"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/crypto/ecies"
	"github.com/ethereum/go-ethereum/rlp"
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
func NewSealedPrivatePayload(encryptedPayload []byte, symmetricKey [][]byte, participants []*ecdsa.PublicKey) SealedPrivatePayload {
	keysToStore := make([][]byte, len(participants))
	for i, key := range participants {
		keysToStore[i] = ecieskey.EncodeEcdsaPubKey(key)
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
	// TxPayload represents the real tx payload which could be an IPFS address or ID of other kind of remote db
	TxPayload []byte
}

// SealPrivatePayload encrypts private tx's payload and sends it to IPFS, then replaces the payload with the address in IPFS.
// Returns an address which could be used to retrieve original payload from IPFS.
func SealPrivatePayload(payload []byte, txNonce uint64, participants []string, remoteDB database.RemoteDatabase) (PayloadReplacement, error) {
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
	remoteDataId, err := remoteDB.Put(bytesToPut)
	if err != nil {
		return PayloadReplacement{}, err
	}

	// Enclose as a PayloadReplacement struct.
	replacement := PayloadReplacement{
		TxPayload:    remoteDataId,
		Participants: participants,
	}
	return replacement, nil
}

// SupportPrivateTx returns a bool value indicating whether it supports private transaction
func SupportPrivateTx() bool {
	return SupportPrivateTxFlag
}

// stringsToPublicKeys converts string to ecies.PublicKey instance.
func stringsToPublicKeys(keys []string) ([]*ecdsa.PublicKey, error) {
	pubKeys := make([]*ecdsa.PublicKey, len(keys))

	for i, p := range keys {
		if p[:2] != "0x" {
			p = "0x" + p
		}
		keyBuf, _ := hexutil.Decode(p)
		pubKey, err := ecieskey.DecodeEcdsaPubKeyFrom(keyBuf)
		if err != nil {
			log.Error("Decode Ecdsa pub key failed", "err", err)
		}
		pubKeys[i] = pubKey
	}
	return pubKeys, nil
}

// sealSymmetricKey sealed symmetric key by encrypting it with participant's public keys one by one.
func sealSymmetricKey(symKey []byte, keys []*ecdsa.PublicKey) [][]byte {
	result := make([][]byte, len(keys))
	for i, key := range keys {
		eciesKey := ecies.ImportECDSAPublic(key)
		encryptedKey, _ := ecieskey.Encrypt(eciesKey, symKey)
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
