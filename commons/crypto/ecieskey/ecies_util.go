package ecieskey

import (
	"crypto/ecdsa"
	"crypto/rand"

	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/crypto/ecies"
)

func Encrypt(publicKey *ecies.PublicKey, data []byte) (m []byte, err error) {
	return ecies.Encrypt(rand.Reader, publicKey, data, nil, nil)
}

func Decrypt(privateKey *ecies.PrivateKey, encryptedData []byte) (m []byte, err error) {
	return privateKey.Decrypt(encryptedData, nil, nil)
}

func DecodeEcdsaPubKeyFrom(ecdsaPublicKeyBytes []byte) (*ecdsa.PublicKey, error) {
	return crypto.UnmarshalPubkey(ecdsaPublicKeyBytes)
}

func EncodeEcdsaPubKey(pub *ecdsa.PublicKey) []byte {
	return crypto.FromECDSAPub(pub)
}

func EncodeEcdsaPrivateKey(prv *ecdsa.PrivateKey) []byte {
	return crypto.FromECDSA(prv)
}

func DecodeEcdsaPrivateKey(ecdsaPrivateKeyBytes []byte) *ecdsa.PrivateKey {
	return crypto.ToECDSAUnsafe(ecdsaPrivateKeyBytes)
}

func ExtractEcdsaPubKeyHexFromKeyPrivateKey(prv *ecdsa.PrivateKey) string {
	bytes := EncodeEcdsaPubKey(&prv.PublicKey)
	return hexutil.Encode(bytes)
}
