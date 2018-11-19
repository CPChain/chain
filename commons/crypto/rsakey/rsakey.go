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

package rsakey

import (
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"fmt"
	"os"
	"path/filepath"

	"bitbucket.org/cpchain/chain/commons/log"
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

// Deprecated: Replace with NewRsaPrivateKey
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
	if err != nil {
		return nil, err
	}
	return &RsaKey{priKey, priBytes, &RsaPublicKey{&priKey.PublicKey, pubBytes}}, nil
}
