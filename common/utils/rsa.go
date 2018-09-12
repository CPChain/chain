package utils

import (
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"encoding/pem"
	"errors"
	"os"
)

func RsaEncrypt(origData []byte, publicKey []byte) ([]byte, error) {
	block, _ := pem.Decode(publicKey)
	if block == nil {
		return nil, errors.New("public key error")
	}
	pubInterface, err := x509.ParsePKIXPublicKey(block.Bytes)
	if err != nil {
		return nil, err
	}
	pub := pubInterface.(*rsa.PublicKey)
	return rsa.EncryptPKCS1v15(rand.Reader, pub, origData)
}

func RsaDecrypt(cipherText []byte, privateKey []byte) ([]byte, error) {
	block, _ := pem.Decode(privateKey)
	if block == nil {
		return nil, errors.New("private key error")
	}
	priv, err := x509.ParsePKCS1PrivateKey(block.Bytes)
	if err != nil {
		return nil, err
	}
	return rsa.DecryptPKCS1v15(rand.Reader, priv, cipherText)
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
	err = pem.Encode(file, block)
	return err
}

func LoadRsaKey(pubPath, priPath string) ([]byte, []byte, error) {
	pub, pubErr := LoadFile(pubPath)
	if pubErr != nil {
		return nil, nil, errors.New("load public key file [" + pubPath + "] failed")
	}
	pri, priErr := LoadFile(priPath)
	if priErr != nil {
		return nil, nil, errors.New("load private key file [" + priPath + "] failed")
	}
	return pub, pri, nil
}
