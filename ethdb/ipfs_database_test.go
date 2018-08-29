package ethdb_test

import (
	"testing"

	"bytes"
	"crypto/sha256"
	"io"
	"io/ioutil"

	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/ethdb"
)

// Fake IPFS for unit test.
type FakeIpfsAdapter struct {
	store map[string][]byte
}

func newFakeIpfsAdapter() *FakeIpfsAdapter {
	return &FakeIpfsAdapter{
		store: map[string][]byte{},
	}
}

func (adapter *FakeIpfsAdapter) Cat(path string) (io.ReadCloser, error) {
	buf := adapter.store[path]
	return ioutil.NopCloser(bytes.NewReader(buf)), nil
}

func (adapter *FakeIpfsAdapter) Add(r io.Reader) (string, error) {
	data, _ := ioutil.ReadAll(r)
	hash := sha256.Sum256(data)
	path := hexutil.Encode(hash[:])
	adapter.store[path] = data[:]
	return path, nil
}

const testDbWrongUrl = "localhost:5002"

var normalContent = []byte("this is a placeholder for private tx payload.")

// Test for putting and getting normal content.
func TestIpfsDbGetPutWithNormalContent(t *testing.T) {
	db := ethdb.NewIpfsDbWithAdapter(newFakeIpfsAdapter())
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

// Test for putting and getting empty content.
func TestIpfsDbGetPutWithEmptyValue(t *testing.T) {
	db := ethdb.NewIpfsDbWithAdapter(newFakeIpfsAdapter())
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

// Test new IPFS database with wrong URL.
func TestIpfsDbWithWrongUrl(t *testing.T) {
	wrongDb := ethdb.NewIpfsDb(testDbWrongUrl)
	_, err := wrongDb.Put(normalContent)
	if err == nil {
		t.Errorf("Wrong url should cause an error.")
	}
}
