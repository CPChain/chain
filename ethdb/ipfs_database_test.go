package ethdb_test

import (
"testing"
	"github.com/ethereum/go-ethereum/ethdb"
	)

type composer struct {
	name 		string
	birthYear 	int
}


const testDbUrl = "localhost:5001"
const testDbWrongUrl = "localhost:5002"
var normalContent = []byte("this is a placeholder for private tx payload.")

func TestIpfsDb_PutGet(t *testing.T) {
	db := ethdb.NewIpfsDb(testDbUrl)
	testIpfsDbWithNormalContent(t, db)
	testIpfsDbWithEmptyValue(t, db)

	testIpfsDbWithWrongUrl(t)
}

// Test for putting and getting normal content
func testIpfsDbWithNormalContent(t *testing.T, db *ethdb.IpfsDatabase) {
	key, err := db.Put(normalContent)
	if key == nil {
		t.Errorf("Normal put operation should return a non-empty key.");
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

// Test for putting and getting empty content
func testIpfsDbWithEmptyValue(t *testing.T, db *ethdb.IpfsDatabase) {
	// putting empty value into db should work as normal
	emptyContent := []byte{}

	key, err := db.Put(emptyContent)
	if key == nil {
		t.Errorf("Putting empty content should return a non-empty key.")
	}
	if err != nil {
		t.Errorf("Putting empty content shoudl succeed and return an nil error.")
	}
	retValue, err := db.Get(key)
	if err != nil {
		t.Errorf("Getting a saved empty content should not return any error.")
	}
	if len(retValue) != 0 {
		t.Errorf("The retrieved content should be empty.")
	}
}

func testIpfsDbWithWrongUrl(t *testing.T) {
	wrongDb := ethdb.NewIpfsDb(testDbWrongUrl)
	_, err := wrongDb.Put(normalContent)
	if err == nil {
		t.Errorf("Wrong url should cause an error.")
	}
}