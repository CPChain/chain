package rsa1

import (
	"testing"

	"flag"

	"os"

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

	pubKey, priKey, err := LoadRsaKey(rsaPubFilePath, rsaPriFilePath)
	assert.Nil(t, err)
	assert.NotNil(t, pubKey)
	assert.NotNil(t, priKey)

	source := "hello,rsa"
	result, err := RsaEncrypt([]byte(source), pubKey)
	assert.Nil(t, err)

	origData, err := RsaDecrypt(result, priKey)
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
