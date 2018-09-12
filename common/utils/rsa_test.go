package utils

import (
	"fmt"
	"testing"

	"flag"

	"os"

	"github.com/stretchr/testify/assert"
)

var (
	rsaPubFilePath = "/tmp/rsa.pub"
	rsaPriFilePath = "/tmp/rsa.pri"
)
var privateKey = []byte(`
-----BEGIN RSA PRIVATE KEY-----
MIICXQIBAAKBgQDZsfv1qscqYdy4vY+P4e3cAtmvppXQcRvrF1cB4drkv0haU24Y
7m5qYtT52Kr539RdbKKdLAM6s20lWy7+5C0DgacdwYWd/7PeCELyEipZJL07Vro7
Ate8Bfjya+wltGK9+XNUIHiumUKULW4KDx21+1NLAUeJ6PeW+DAkmJWF6QIDAQAB
AoGBAJlNxenTQj6OfCl9FMR2jlMJjtMrtQT9InQEE7m3m7bLHeC+MCJOhmNVBjaM
ZpthDORdxIZ6oCuOf6Z2+Dl35lntGFh5J7S34UP2BWzF1IyyQfySCNexGNHKT1G1
XKQtHmtc2gWWthEg+S6ciIyw2IGrrP2Rke81vYHExPrexf0hAkEA9Izb0MiYsMCB
/jemLJB0Lb3Y/B8xjGjQFFBQT7bmwBVjvZWZVpnMnXi9sWGdgUpxsCuAIROXjZ40
IRZ2C9EouwJBAOPjPvV8Sgw4vaseOqlJvSq/C/pIFx6RVznDGlc8bRg7SgTPpjHG
4G+M3mVgpCX1a/EU1mB+fhiJ2LAZ/pTtY6sCQGaW9NwIWu3DRIVGCSMm0mYh/3X9
DAcwLSJoctiODQ1Fq9rreDE5QfpJnaJdJfsIJNtX1F+L3YceeBXtW0Ynz2MCQBI8
9KP274Is5FkWkUFNKnuKUK4WKOuEXEO+LpR+vIhs7k6WQ8nGDd4/mujoJBr5mkrw
DPwqA3N5TMNDQVGv8gMCQQCaKGJgWYgvo3/milFfImbp+m7/Y3vCptarldXrYQWO
AQjxwc71ZGBFDITYvdgJM1MTqc8xQek1FXn1vfpy2c6O
-----END RSA PRIVATE KEY-----
`)

var publicKey = []byte(`
-----BEGIN PUBLIC KEY-----
MIGfMA0GCSqGSIb3DQEBAQUAA4GNADCBiQKBgQDZsfv1qscqYdy4vY+P4e3cAtmv
ppXQcRvrF1cB4drkv0haU24Y7m5qYtT52Kr539RdbKKdLAM6s20lWy7+5C0Dgacd
wYWd/7PeCELyEipZJL07Vro7Ate8Bfjya+wltGK9+XNUIHiumUKULW4KDx21+1NL
AUeJ6PeW+DAkmJWF6QIDAQAB
-----END PUBLIC KEY-----
`)

func TestRsaEncryptAndDecrypt(t *testing.T) {
	source := "hello,rsa"
	result, err := RsaEncrypt([]byte(source), publicKey)
	if err != nil {
		panic(err)
	}

	origData, err := RsaDecrypt(result, privateKey)
	if err != nil {
		panic(err)
	}
	got := string(origData)
	fmt.Println(got)
	assert.Equal(t, source, got)
}

func TestGenerateAndLoadRsaKey(t *testing.T) {
	// clean test file
	os.Remove(rsaPriFilePath)
	os.Remove(rsaPubFilePath)

	var bits int
	flag.IntVar(&bits, "b", 2048, "key length,default is 1024")
	err := GenerateRsaKey(rsaPubFilePath, rsaPriFilePath, bits)
	assert.Nil(t, err)

	pubKeyBytes, priKeyBytes, err := LoadRsaKey(rsaPubFilePath, rsaPriFilePath)
	assert.Nil(t, err)
	assert.NotNil(t, pubKeyBytes)
	assert.NotNil(t, priKeyBytes)
	fmt.Println("pub:", string(pubKeyBytes))
	fmt.Println("pri:", string(priKeyBytes))

	source := "hello,rsa"
	result, err := RsaEncrypt([]byte(source), pubKeyBytes)
	assert.Nil(t, err)

	origData, err := RsaDecrypt(result, priKeyBytes)
	assert.Nil(t, err)
	got := string(origData)
	assert.Equal(t, source, got)
}

func TestLoadRsaKey(t *testing.T) {
	pubBytes, priBytes, err := LoadRsaKey("/tmp/notexist", "/tmp/notexist1")
	assert.Nil(t, pubBytes)
	assert.Nil(t, priBytes)
	assert.NotNil(t, err)
}

func TestLoadRsaKey1(t *testing.T) {
	_, err := os.Create(rsaPriFilePath)
	pubBytes, priBytes, err := LoadRsaKey(rsaPubFilePath, "/tmp/notexist1")
	assert.Nil(t, pubBytes)
	assert.Nil(t, priBytes)
	assert.NotNil(t, err)
}

func TestLoadRsaKey2(t *testing.T) {
	_, err := os.Create(rsaPriFilePath)
	pubBytes, priBytes, err := LoadRsaKey("/tmp/notexist1", rsaPriFilePath)
	assert.Nil(t, pubBytes)
	assert.Nil(t, priBytes)
	assert.NotNil(t, err)
}
