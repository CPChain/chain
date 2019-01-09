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
	"bytes"
	"crypto/rsa"
	"flag"
	"fmt"
	"math/big"
	"os"
	"testing"

	"github.com/ethereum/go-ethereum/rlp"
	"github.com/stretchr/testify/assert"
)

var (
	rsaPriFilePath = "/tmp/rsa.pri"
)

func TestGenerateAndloadRsaKey(t *testing.T) {
	// clean test file
	os.Remove(rsaPriFilePath)

	var bits int
	flag.IntVar(&bits, "b", 2048, "key length,default is 1024")
	err := generateRsaKey(rsaPriFilePath, bits)
	assert.Nil(t, err)

	rsaKey, err := NewRsaKey("/tmp")

	assert.Nil(t, err)
	source := "hello,rsa"
	result, err := rsaKey.RsaEncrypt([]byte(source))
	assert.Nil(t, err)

	origData, err := rsaKey.RsaDecrypt(result)
	assert.Nil(t, err)
	got := string(origData)
	assert.Equal(t, source, got)
}

func TestLoadRsaKey(t *testing.T) {
	publicKey, privateKey, pubBytes, priBytes, err := loadRsaKey("/tmp/notexist")
	assert.Nil(t, publicKey)
	assert.Nil(t, privateKey)
	assert.Nil(t, pubBytes)
	assert.Nil(t, priBytes)
	assert.NotNil(t, err)
}

func TestLoadRsaKey1(t *testing.T) {
	_, err := os.Create(rsaPriFilePath)
	publicKey, privateKey, pubBytes, priBytes, err := loadRsaKey("/tmp/notexist1")
	assert.Nil(t, publicKey)
	assert.Nil(t, privateKey)
	assert.Nil(t, pubBytes)
	assert.Nil(t, priBytes)
	assert.NotNil(t, err)
}

func TestLoadRsaKey2(t *testing.T) {
	_, err := os.Create(rsaPriFilePath)
	publicKey, privateKey, pubBytes, priBytes, err := loadRsaKey(rsaPriFilePath)
	assert.Nil(t, publicKey)
	assert.Nil(t, privateKey)
	assert.Nil(t, pubBytes)
	assert.Nil(t, priBytes)
	assert.NotNil(t, err)
}

func TestLoadRsaKey3(t *testing.T) {

	publicKey, privateKey, pubBytes, priBytes, _ := loadRsaKey("./testdata/rsa_pri.pem")
	assert.NotNil(t, publicKey)
	assert.NotNil(t, privateKey)
	assert.NotNil(t, pubBytes)
	assert.NotNil(t, priBytes)

	pe := publicKey.E
	pn := publicKey.N
	fmt.Println("pe", pe)
	fmt.Println("pn", pn)
	fmt.Println("pn bytes:", pn.Bytes())

	assert.Equal(t, 65537, pe)
	assert.Equal(t, "23890870258313684719997559149118646866034264027284543849655977565335672901131694672031986558222967651040937456863897188902350149743460372035115917425121055499959205524503641445566613872072624737697880021501494593230760549001864350649979843223936492367180376489011010132628122353612959073423709853490834312548051078796845317450031898275450664770638585201541192510378468247475310882169189566639310601765161352041463947741408761376023315235251874366110545395784615598672067093245714300181812101376047774920109259909617517000020556608468502520985216910666467508585869795380650276754191879595756017747747304493068258340411", string(pn.String()))

	z := new(big.Int)
	z.SetBytes(pn.Bytes())
	fmt.Println("z:", z)

	pk := rsa.PublicKey{
		N: z,
		E: 65537,
	}
	fmt.Println("pk:", pk)
	assert.NotNil(t, pk)
}

func TestEncodeDecodeRsaPublicKey(t *testing.T) {

	publicKey, privateKey, pubBytes, priBytes, _ := loadRsaKey("./testdata/rsa_pri.pem")
	assert.NotNil(t, publicKey)
	assert.NotNil(t, privateKey)
	assert.NotNil(t, pubBytes)
	assert.NotNil(t, priBytes)
	pe := publicKey.E
	pn := publicKey.N

	assert.Equal(t, 65537, pe)
	assert.Equal(t, "23890870258313684719997559149118646866034264027284543849655977565335672901131694672031986558222967651040937456863897188902350149743460372035115917425121055499959205524503641445566613872072624737697880021501494593230760549001864350649979843223936492367180376489011010132628122353612959073423709853490834312548051078796845317450031898275450664770638585201541192510378468247475310882169189566639310601765161352041463947741408761376023315235251874366110545395784615598672067093245714300181812101376047774920109259909617517000020556608468502520985216910666467508585869795380650276754191879595756017747747304493068258340411", string(pn.String()))

	publicKeyBytes, _ := rlp.EncodeToBytes(publicKey)
	fmt.Println("publicKey:", string(publicKeyBytes))

	z := new(big.Int)
	z.SetBytes(pn.Bytes())
	fmt.Println("z:", z)

	pk := rsa.PublicKey{
		N: z,
		E: 65537,
	}
	fmt.Println("pk:", pk)
	assert.NotNil(t, pk)
}

func TestNewRsaPrivateKey(t *testing.T) {

	publicKey, privateKey, pubBytes, priBytes, _ := loadRsaKey("./testdata/rsa_pri.pem")
	assert.NotNil(t, publicKey)
	assert.NotNil(t, privateKey)
	assert.NotNil(t, pubBytes)
	assert.NotNil(t, priBytes)

	// bb := hex.EncodeToString(priBytes)
	// fmt.Println(":::", bb)
	// newPriBytes, err := hex.DecodeString(bb)
	// priBytes = newPriBytes

	rsaKey, err := NewRsaPrivateKey(priBytes)
	assert.Nil(t, err)
	assert.NotNil(t, rsaKey.PublicKey)
	assert.NotNil(t, rsaKey.PublicKey.RsaPublicKeyBytes)
	assert.NotNil(t, rsaKey.PublicKey.RsaPublicKey)
	assert.NotNil(t, rsaKey.PrivateKey)
	assert.NotNil(t, rsaKey.PrivateKeyBytes)

	assert.Equal(t, priBytes, rsaKey.PrivateKeyBytes)
	assert.Equal(t, publicKey, rsaKey.PublicKey.RsaPublicKey)
	assert.Equal(t, 0, bytes.Compare(pubBytes, rsaKey.PublicKey.RsaPublicKeyBytes))
}

func TestLoadFile(t *testing.T) {
	bytes, err := LoadFile("/_30mbkeaetmp/notexist")
	assert.Nil(t, bytes)
	assert.NotNil(t, err)
}

func TestBytes2PublicKey(t *testing.T) {
	key, err := bytes2PublicKey([]byte("errorbytes"))
	assert.NotNil(t, err)
	assert.Nil(t, key)
}
