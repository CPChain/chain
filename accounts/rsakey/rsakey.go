package rsakey

import (
	"bitbucket.org/cpchain/chain/commons/log"
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"fmt"
	"os"
	"path/filepath"
)

type RsaPublicKey struct {
	// Rsa public key
	RsaPublicKey *rsa.PublicKey

	// Rsa public key
	RsaPublicKeyBytes []byte
}

type RsaKey struct {
	// Rsa private key
	PrivateKey *rsa.PrivateKey

	// Rsa private key
	PrivateKeyBytes []byte

	// Rsa public key
	PublicKey *RsaPublicKey
}

// create new rsa key
func CreateRsaKey() (*RsaKey, error) {
	pub, pri, pubBytes, priBytes, err := generateDerRsaKey(2048)
	if err == nil {
		return &RsaKey{pri, priBytes, &RsaPublicKey{pub, pubBytes}}, nil
	}
	return nil, err
}

// NewRsaKey creates a keystore for the given directory.
func NewRsaKey(rsaDir string) (*RsaKey, error) {
	if err := os.MkdirAll(rsaDir, 0700); err != nil {
		return nil, err
	}
	rsaPriPath := filepath.Join(rsaDir, "rsa_pri.pem")

	// Load RSA key
	if pub, pri, pubBytes, priBytes, err := loadRsaKey(rsaPriPath); err == nil {
		return &RsaKey{pri, priBytes, &RsaPublicKey{pub, pubBytes}}, nil
	}
	// No persistent key found, generate and store a new one.
	log.Info(fmt.Sprintf("file not found. rsaPriPath:%v", rsaPriPath))
	err := generateRsaKey(rsaPriPath, 2048)
	if err != nil {
		log.Error(fmt.Sprintf("Failed to persist rsa key: %v", err))
		return nil, err
	}
	if pub, pri, pubBytes, priBytes, err := loadRsaKey(rsaPriPath); err == nil {
		return &RsaKey{pri, priBytes, &RsaPublicKey{pub, pubBytes}}, nil
	}
	log.Error(fmt.Sprintf("load rsa key fail:%v", err))
	return nil, err
}

func (ks *RsaKey) RsaEncrypt(origData []byte) ([]byte, error) {
	return ks.PublicKey.RsaEncrypt(origData)
}

func (ks *RsaKey) RsaDecrypt(cipherText []byte) ([]byte, error) {
	return rsa.DecryptPKCS1v15(rand.Reader, ks.PrivateKey, cipherText)
}

func (ks *RsaPublicKey) RsaEncrypt(origData []byte) ([]byte, error) {
	return rsa.EncryptPKCS1v15(rand.Reader, ks.RsaPublicKey, origData)
}

func NewRsaPublicKey(bs []byte) (*RsaPublicKey, error) {
	pubKey, err := bytes2PublicKey(bs)
	if err != nil {
		return nil, err
	}
	return &RsaPublicKey{pubKey, bs}, err
}

func NewRsaPrivateKey(priKeyBytes []byte) (*RsaKey, error) {
	if len(priKeyBytes) == 0 {
		return nil, nil
	}
	priKey, err := bytes2PrivateKey(priKeyBytes)
	if err != nil {
		return nil, err
	}
	priBytes := x509.MarshalPKCS1PrivateKey(priKey)
	pubBytes := x509.MarshalPKCS1PublicKey(&priKey.PublicKey)
	// pubBytes, err := x509.MarshalPKIXPublicKey(publicKey)
	if err != nil {
		return nil, err
	}
	return &RsaKey{priKey, priBytes, &RsaPublicKey{&priKey.PublicKey, pubBytes}}, nil
}
