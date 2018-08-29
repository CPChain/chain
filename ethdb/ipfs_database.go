package ethdb

import (
	"bytes"

	"io"

	"io/ioutil"

	"github.com/ipfs/go-ipfs-api"
)

// IPFS-based database.
type IpfsDatabase struct {
	adapter IpfsAdapter
}

// Adapter for IPFS access and make a room for weaving fake IPFS in unit test.
type IpfsAdapter interface {
	// Read data from IPFS.
	Cat(path string) (io.ReadCloser, error)
	// Add/save data to IPFS.
	Add(r io.Reader) (string, error)
}

// Create a new IpfsDatabase instance with given url which is the IPFS node's API url.
func NewIpfsDb(url string) *IpfsDatabase {
	s := IpfsAdapter(shell.NewShell(url))
	return NewIpfsDbWithAdapter(s)
}

// Create a new IpfsDatabase instance with given IPFS adapter.
func NewIpfsDbWithAdapter(adapter IpfsAdapter) *IpfsDatabase {
	return &IpfsDatabase{
		adapter: adapter,
	}
}

// Retrieve data from IPFS with given key.
func (db *IpfsDatabase) Get(key []byte) ([]byte, error) {
	k := string(key[:])
	reader, err := db.adapter.Cat(k)
	if err != nil {
		return nil, err
	}

	return ioutil.ReadAll(reader)
}

// Save data to IPFS and return key(internally it is a hash).
func (db *IpfsDatabase) Put(value []byte) ([]byte, error) {
	reader := bytes.NewBuffer(value)
	hash, err := db.adapter.Add(reader)

	if err != nil {
		return nil, err
	} else {
		return []byte(hash), nil
	}
}
