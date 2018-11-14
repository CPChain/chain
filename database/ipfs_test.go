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

package database

import (
	"testing"
)

const (
	testDbWrongURL  = "localhost:5002"
	unexistIpfsAddr = "QmPam2fqFP7eTmnUJn2BX1GSBXpVZ5zqDpVjWQ3T88AEd3"
)

var normalContent = []byte("this is a placeholder for private tx payload.")

// TestIpfsDbGetPutWithNormalContent tests for putting and getting normal content.
func TestIpfsDbGetPutWithNormalContent(t *testing.T) {
	db := NewIpfsDbWithAdapter(NewFakeIpfsAdapter())
	key, err := db.Put(normalContent)
	if key == nil {
		t.Errorf("Normal put operation should return a non-empty key.")
	}
	if err != nil {
		t.Errorf("Normal put operation should succeed and return an nil error.")
	}
	retValue, err := db.Get(key)
	if err != nil {
		t.Errorf("Getting a successfully saved normal content should not return any error.")
	}
	if string(normalContent) != string(retValue) {
		t.Errorf("Retrieved content %v does not equal to original value %v", retValue, normalContent)
	}
}

// TestIpfsDbGetPutWithEmptyValue tests for putting and getting empty content.
func TestIpfsDbGetPutWithEmptyValue(t *testing.T) {
	db := NewIpfsDbWithAdapter(NewFakeIpfsAdapter())
	// putting empty value into db should work as normal
	emptyContent := []byte{}

	key, err := db.Put(emptyContent)
	if key == nil {
		t.Errorf("Putting empty content should return a non-empty key.")
	}
	if err != nil {
		t.Errorf("Putting empty content should succeed and return an nil error.")
	}
	retValue, err := db.Get(key)
	if err != nil {
		t.Errorf("Getting a saved empty content should not return any error.")
	}
	if len(retValue) != 0 {
		t.Errorf("The retrieved content should be empty.")
	}
}

// TestIpfsDbWithWrongUrl tests new IPFS database with wrong URL.
func TestIpfsDbWithWrongUrl(t *testing.T) {
	wrongDb := NewIpfsDB(testDbWrongURL)
	_, err := wrongDb.Put(normalContent)
	if err == nil {
		t.Errorf("Wrong url should cause an error.")
	}
}

// TestIpfsDbWithWrongUrl tests new IPFS database with wrong URL.
func TestIpfsDatabase_Get(t *testing.T) {
	db := NewIpfsDbWithAdapter(NewFakeIpfsAdapter())
	v, err := db.Get([]byte("abcdef"))
	if err == nil {
		t.Errorf("Getting for unexsitent key should produce an error.")
	}
	if v != nil {
		t.Error("The value should be nil when error occurs.")
	}
}

func TestIpfsDatabase_Has(t *testing.T) {
	db := NewIpfsDbWithAdapter(NewFakeIpfsAdapter())

	key, _ := db.Put([]byte{1, 2, 3, 4, 5, 6, 7, 8})
	if !db.Has([]byte(key)) {
		t.Error("The result of Has() should be true when the data to retrieve does exist.")
	}

	if db.Has([]byte(unexistIpfsAddr)) {
		t.Error("The result of Has() should be false when the data to retrieve does not exist.")
	}

}

func TestIpfsDatabase_Discard(t *testing.T) {
	db := NewIpfsDbWithAdapter(NewFakeIpfsAdapter())
	key, _ := db.Put([]byte{1, 2, 3, 4, 5, 6, 7, 8})

	if db.Discard(key) != nil {
		t.Error("Discard should not throw error when the data to discard does exist.")
	}

	if db.Has(key) {
		t.Error("The data should not exist after discard.")
	}
}
