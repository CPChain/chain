// Copyright 2016 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package keystore

import (
	"io/ioutil"
	"reflect"
	"testing"

	"github.com/ethereum/go-ethereum/common"
)

const (
	veryLightScryptN = 2
	veryLightScryptP = 1
)

// Tests that a json key file can be decrypted and encrypted in multiple rounds.
func TestKeyEncryptDecrypt(t *testing.T) {
	keyjson, err := ioutil.ReadFile("testdata/very-light-scrypt.json")
	if err != nil {
		t.Fatal(err)
	}
	password := ""
	address := common.HexToAddress("45dea0fb0bba44f4fcf290bba71fd57d7117cbb8")

	// Do a few rounds of decryption and encryption
	for i := 0; i < 3; i++ {
		// Try a bad password first
		if _, err := DecryptKey(keyjson, password+"bad"); err == nil {
			t.Errorf("test %d: json key decrypted with bad password", i)
		}
		// Decrypt with the correct password
		key, err := DecryptKey(keyjson, password)
		if err != nil {
			t.Fatalf("test %d: json key failed to decrypt: %v", i, err)
		}
		if key.Address != address {
			t.Errorf("test %d: key address mismatch: have %x, want %x", i, key.Address, address)
		}
		// Recrypt with a new password and start over
		password += "new data appended"
		if keyjson, err = EncryptKey(key, password, veryLightScryptN, veryLightScryptP); err != nil {
			t.Errorf("test %d: failed to recrypt key %v", i, err)
		}
	}
}

func TestMergeBytes(t *testing.T) {
	b1, b2 := []byte("bbb1"), []byte("aaaccc2")
	b3 := mergeBytes(b1, b2)
	expected := []byte("bbb1" + "aaaccc2")
	if !reflect.DeepEqual(b3, expected) {
		t.Errorf("merge bytes error: have %x, want %x", b3, expected)
	}
}

func TestDecryptKeyTestnet(t *testing.T) {
	address := common.HexToAddress("2a15146f434c0205cfae639de2ac4bb543539b24")
	keyjson, err := ioutil.ReadFile("../../examples/cpchain/conf-testnet/keys/key1")
	if err != nil {
		t.Skip("file not found.skip.")
	}
	password := "3407868881_5037"
	key, err := DecryptKey(keyjson, password)
	if err != nil {
		t.Fatalf("test %d: json key failed to decrypt: %v", 1, err)
	}
	if key.Address != address {
		t.Errorf("test %d: key address mismatch: have %x, want %x", 1, key.Address, address)
	}

}

func TestDecryptKeyDev(t *testing.T) {
	address := common.HexToAddress("e94b7b6c5a0e526a4d97f9768ad6097bde25c62a")
	keyjson, err := ioutil.ReadFile("../../examples/cpchain/conf-dev/keys/key1")
	if err != nil {
		t.Fatal(err)
	}
	password := "password"
	key, err := DecryptKey(keyjson, password)
	if err != nil {
		t.Fatalf("test %d: json key failed to decrypt: %v", 1, err)
	}
	if key.Address != address {
		t.Errorf("test %d: key address mismatch: have %x, want %x", 1, key.Address, address)
	}
}
