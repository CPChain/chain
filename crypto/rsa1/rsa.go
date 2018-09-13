package rsa1

import (
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"encoding/pem"
	"errors"
	"os"
)

func RsaEncrypt(origData []byte, publicKey *rsa.PublicKey) ([]byte, error) {
	return rsa.EncryptPKCS1v15(rand.Reader, publicKey, origData)
}

func RsaDecrypt(cipherText []byte, privateKey *rsa.PrivateKey) ([]byte, error) {
	return rsa.DecryptPKCS1v15(rand.Reader, privateKey, cipherText)
}

func GenerateRsaKey(pubKeyPath, privateKeyPath string, bits int) error {
	// generate public key
	privateKey, err := rsa.GenerateKey(rand.Reader, bits)
	if err != nil {
		return err
	}
	priBytes := x509.MarshalPKCS1PrivateKey(privateKey)
	block := &pem.Block{
		Type:  "private key",
		Bytes: priBytes,
	}
	file, err := os.Create(privateKeyPath)
	if err != nil {
		return err
	}
	defer file.Close()
	err = pem.Encode(file, block)
	if err != nil {
		return err
	}
	// generate public key
	publicKey := &privateKey.PublicKey
	pubBytes, err := x509.MarshalPKIXPublicKey(publicKey)
	if err != nil {
		return err
	}
	block = &pem.Block{
		Type:  "public key",
		Bytes: pubBytes,
	}
	file, err = os.Create(pubKeyPath)
	if err != nil {
		return err
	}
	defer file.Close()
	err = pem.Encode(file, block)
	return err
}

func LoadRsaKey(pubPath, priPath string) (*rsa.PublicKey, *rsa.PrivateKey, error) {
	pub, pubErr := LoadFile(pubPath)
	if pubErr != nil {
		return nil, nil, errors.New("load public key file [" + pubPath + "] failed")
	}
	block, _ := pem.Decode(pub)
	if block == nil {
		return nil, nil, errors.New("decode public key error")
	}
	pubInterface, err := x509.ParsePKIXPublicKey(block.Bytes)
	if err != nil {
		return nil, nil, err
	}

	pubKey := pubInterface.(*rsa.PublicKey)

	pri, priErr := LoadFile(priPath)
	if priErr != nil {
		return nil, nil, errors.New("load private key file [" + priPath + "] failed")
	}
	priBlock, _ := pem.Decode(pri)
	if block == nil {
		return nil, nil, errors.New("private key error")
	}
	privKey, err := x509.ParsePKCS1PrivateKey(priBlock.Bytes)
	if err != nil {
		return nil, nil, err
	}

	return pubKey, privKey, nil
}
