package ecieskey

import (
	"fmt"
	"testing"

	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/crypto/ecies"
	"github.com/stretchr/testify/assert"
)

var (
	ecdsaPrivateKey, _  = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	ecdsaPrivateKey1, _ = crypto.HexToECDSA("8a1f9a8f95be41cd7ccb6168179afb4504aefe388d1e14474d32c45c72ce7b7a")
	data                = []byte("testme")
)

func TestEncryptAndDecrypt(t *testing.T) {
	// encrypt
	eciesPublicKey := ecies.ImportECDSAPublic(&ecdsaPrivateKey.PublicKey)

	encryptedData, err := Encrypt(eciesPublicKey, data)
	assert.Nil(t, err)

	// decrypt
	eciesPrivateKey := ecies.ImportECDSA(ecdsaPrivateKey)

	decryptedData, err := Decrypt(eciesPrivateKey, encryptedData)
	fmt.Println("decryptedData:", decryptedData)
	assert.Equal(t, data, decryptedData)
}

func TestEncodeAndDecodePublicKey(t *testing.T) {
	ecdsaPublicKeyBytes := EncodeEcdsaPubKey(&ecdsaPrivateKey.PublicKey)
	assert.NotNil(t, ecdsaPublicKeyBytes)
	// replace rsa public key with Ecdsa PubKey
	fmt.Println("ecdsaPublicKeyBytes:", hexutil.Encode(ecdsaPublicKeyBytes))

	pubKey, err := DecodeEcdsaPubKeyFrom(ecdsaPublicKeyBytes)
	assert.Nil(t, err)
	assert.NotNil(t, pubKey)
}

func TestEncodeAndDecodePublicKey1(t *testing.T) {
	ecdsaPublicKeyBytes := EncodeEcdsaPubKey(&ecdsaPrivateKey1.PublicKey)
	assert.NotNil(t, ecdsaPublicKeyBytes)
	// replace rsa public key with Ecdsa PubKey
	fmt.Println("ecdsaPublicKeyBytes:", hexutil.Encode(ecdsaPublicKeyBytes))

	pubKey, err := DecodeEcdsaPubKeyFrom(ecdsaPublicKeyBytes)
	assert.Nil(t, err)
	assert.NotNil(t, pubKey)
}

func TestExtractEcdsaPubKeyHexFromKeyPrivateKey(t *testing.T) {
	str := ExtractEcdsaPubKeyHexFromKeyPrivateKey(ecdsaPrivateKey)
	assert.Equal(t,
		"0x04ca634cae0d49acb401d8a4c6b6fe8c55b70d115bf400769cc1400f3258cd31387574077f301b421bc84df7266c44e9e6d569fc56be00812904767bf5ccd1fc7f",
		str)
}

func TestEncodeEcdsaPrivateKey(t *testing.T) {
	bytes := EncodeEcdsaPrivateKey(ecdsaPrivateKey)
	str := hexutil.Encode(bytes)
	fmt.Println("ecdsaPrivateKeyBytes:", str)
	assert.Equal(t, "0xb71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291", str)
}
