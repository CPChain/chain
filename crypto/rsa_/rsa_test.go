package rsa_

import (
	"testing"

	"flag"

	"os"

	"fmt"

	"crypto/rsa"

	"math/big"

	"github.com/ethereum/go-ethereum/rlp"
	"github.com/stretchr/testify/assert"
)

var (
	rsaPubFilePath = "/tmp/rsa.pub"
	rsaPriFilePath = "/tmp/rsa.pri"
)

func TestGenerateAndLoadRsaKey(t *testing.T) {
	// clean test file
	os.Remove(rsaPriFilePath)
	os.Remove(rsaPubFilePath)

	var bits int
	flag.IntVar(&bits, "b", 2048, "key length,default is 1024")
	err := GenerateRsaKey(rsaPubFilePath, rsaPriFilePath, bits)
	assert.Nil(t, err)

	publicKey, privateKey, pubBytes, priBytes, err := LoadRsaKey(rsaPubFilePath, rsaPriFilePath)
	assert.Nil(t, err)
	assert.NotNil(t, publicKey)
	assert.NotNil(t, privateKey)
	assert.NotNil(t, pubBytes)
	assert.NotNil(t, priBytes)

	source := "hello,rsa"
	result, err := RsaEncrypt([]byte(source), publicKey)
	assert.Nil(t, err)

	origData, err := RsaDecrypt(result, privateKey)
	assert.Nil(t, err)
	got := string(origData)
	assert.Equal(t, source, got)
}

func TestLoadRsaKey(t *testing.T) {
	publicKey, privateKey, pubBytes, priBytes, err := LoadRsaKey("/tmp/notexist", "/tmp/notexist1")
	assert.Nil(t, publicKey)
	assert.Nil(t, privateKey)
	assert.Nil(t, pubBytes)
	assert.Nil(t, priBytes)
	assert.NotNil(t, err)
}

func TestLoadRsaKey1(t *testing.T) {
	_, err := os.Create(rsaPriFilePath)
	publicKey, privateKey, pubBytes, priBytes, err := LoadRsaKey(rsaPubFilePath, "/tmp/notexist1")
	assert.Nil(t, publicKey)
	assert.Nil(t, privateKey)
	assert.Nil(t, pubBytes)
	assert.Nil(t, priBytes)
	assert.NotNil(t, err)
}

func TestLoadRsaKey2(t *testing.T) {
	_, err := os.Create(rsaPriFilePath)
	publicKey, privateKey, pubBytes, priBytes, err := LoadRsaKey("/tmp/notexist1", rsaPriFilePath)
	assert.Nil(t, publicKey)
	assert.Nil(t, privateKey)
	assert.Nil(t, pubBytes)
	assert.Nil(t, priBytes)
	assert.NotNil(t, err)
}

func TestLoadRsaKey3(t *testing.T) {

	publicKey, privateKey, pubBytes, priBytes, _ := LoadRsaKey("./testdata/rsa_pub.pem", "./testdata/rsa_pri.pem")
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

	publicKey, privateKey, pubBytes, priBytes, _ := LoadRsaKey("./testdata/rsa_pub.pem", "./testdata/rsa_pri.pem")
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
