// Copyright 2018 The cpchain authors

package keystore

import (
	"bytes"
	"encoding/hex"
	"encoding/json"

	"github.com/ethereum/go-ethereum/crypto"
)

// extra mac value
func ExtraDiffMac(keyjson []byte, auth string) (origMac, calcMac []byte) {
	m := make(map[string]interface{})
	if err := json.Unmarshal(keyjson, &m); err != nil {
		return nil, nil
	}
	k := new(encryptedKeyJSONV3)
	if err := json.Unmarshal(keyjson, k); err != nil {
		return nil, nil
	}

	origMac, _ = hex.DecodeString(k.Crypto.MAC)
	cipherText, _ := hex.DecodeString(k.Crypto.CipherText)
	rsaCipherText, _ := hex.DecodeString(k.Crypto.RsaCipherText)
	derivedKey, _ := getKDFKey(k.Crypto, auth)
	macSource := mergeBytes(cipherText, rsaCipherText)
	calculatedMAC := crypto.Keccak256(derivedKey[16:32], macSource)
	if !bytes.Equal(calculatedMAC, origMac) {
		return origMac, calculatedMAC
	}
	return origMac, origMac
}
