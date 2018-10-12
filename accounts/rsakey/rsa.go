package rsakey

import (
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"encoding/pem"
	"errors"
	"os"

	"github.com/ethereum/go-ethereum/log"
)

func generateRsaKey(pubKeyPath, privateKeyPath string, bits int) error {
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

func loadRsaKey(pubPath, priPath string) (*rsa.PublicKey, *rsa.PrivateKey, []byte, []byte, error) {
	publicBlock, err := loadKeyFile(pubPath)
	if err != nil {
		return nil, nil, nil, nil, err
	}
	priBlock, err := loadKeyFile(priPath)
	if err != nil {
		return nil, nil, nil, nil, err
	}

	pubInterface, err := bytes2PublicKey(publicBlock.Bytes)
	if err != nil {
		return nil, nil, nil, nil, err
	}

	privateKey, err := bytes2PrivateKey(priBlock.Bytes)
	if err != nil {
		return nil, nil, nil, nil, err
	}
	return pubInterface, privateKey, publicBlock.Bytes, priBlock.Bytes, nil
}

func bytes2PrivateKey(bs []byte) (*rsa.PrivateKey, error) {
	privateKey, err := x509.ParsePKCS1PrivateKey(bs)
	return privateKey, err
}

func bytes2PublicKey(bs []byte) (*rsa.PublicKey, error) {
	publicKey, err := x509.ParsePKIXPublicKey(bs)
	if err != nil {
		return nil, err
	}
	return publicKey.(*rsa.PublicKey), err
}

func loadKeyFile(path string) (*pem.Block, error) {
	keyBytes, pubErr := LoadFile(path)
	log.Info("keyBytes length:", len(keyBytes))
	if pubErr != nil {
		return nil, errors.New("load key file [" + path + "] failed")
	}
	block, _ := pem.Decode(keyBytes)
	if block == nil {
		return nil, errors.New("decode key error")
	}
	return block, pubErr
}
