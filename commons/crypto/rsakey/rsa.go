package rsakey

import (
	"bitbucket.org/cpchain/chain/commons/log"
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"encoding/pem"
	"errors"
	"io/ioutil"
	"os"
)

func generateDerRsaKey(bits int) (*rsa.PublicKey, *rsa.PrivateKey, []byte, []byte, error) {
	privateKey, err := rsa.GenerateKey(rand.Reader, bits)
	if err != nil {
		return nil, nil, nil, nil, err
	}
	priBytes := x509.MarshalPKCS1PrivateKey(privateKey)
	// generate public key
	publicKey := &privateKey.PublicKey
	pubBytes := x509.MarshalPKCS1PublicKey(publicKey)
	return publicKey, privateKey, pubBytes, priBytes, err
}

func generateRsaKey(privateKeyPath string, bits int) error {
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
	return err
}

func loadRsaKey(priPath string) (*rsa.PublicKey, *rsa.PrivateKey, []byte, []byte, error) {
	priBlock, err := loadKeyFile(priPath)
	if err != nil {
		return nil, nil, nil, nil, err
	}

	privateKey, err := bytes2PrivateKey(priBlock.Bytes)
	if err != nil {
		return nil, nil, nil, nil, err
	}
	publicKey := &privateKey.PublicKey
	pubBytes := x509.MarshalPKCS1PublicKey(publicKey)
	return publicKey, privateKey, pubBytes, priBlock.Bytes, nil
}

func bytes2PrivateKey(bs []byte) (*rsa.PrivateKey, error) {
	privateKey, err := x509.ParsePKCS1PrivateKey(bs)
	return privateKey, err
}

func bytes2PublicKey(bs []byte) (*rsa.PublicKey, error) {
	publicKey, err := x509.ParsePKCS1PublicKey(bs)
	if err != nil {
		return nil, err
	}
	return publicKey, err
}

func loadKeyFile(path string) (*pem.Block, error) {
	keyBytes, pubErr := LoadFile(path)
	if pubErr != nil {
		return nil, errors.New("load key file [" + path + "] failed")
	}
	block, _ := pem.Decode(keyBytes)
	if block == nil {
		return nil, errors.New("decode key error")
	}
	return block, pubErr
}

func LoadFile(path string) ([]byte, error) {
	b, err := ioutil.ReadFile(path)
	if err != nil {
		log.Info("file ", path, " not found.")
		return nil, err
	}
	return b, nil
}
