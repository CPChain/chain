package ethdb

import (
	"testing"
)

const testDbWrongURL = "localhost:5002"

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
	wrongDb := NewIpfsDb(testDbWrongURL)
	_, err := wrongDb.Put(normalContent)
	if err == nil {
		t.Errorf("Wrong url should cause an error.")
	}
}
