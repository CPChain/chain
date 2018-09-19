package ethdb

import (
	"bytes"
	"crypto/sha256"
	"io"
	"io/ioutil"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/common/hexutil"
	"github.com/ipfs/go-ipfs-api"
	"github.com/pkg/errors"
)

const ipfsTimeout = 3

// IpfsAdapter represents an adapter for IPFS access.
// It also makes a room for weaving fake IPFS in unit test.
type IpfsAdapter interface {
	// Cat reads data from IPFS.
	Cat(path string) (io.ReadCloser, error)
	// Add adds and pin data to IPFS.
	Add(r io.Reader) (string, error)
	// Unpin unpins the data from IPFS, unpinned data may be removed by GC in future.
	Unpin(path string) error
}

// IpfsDatabase is a IPFS-based database.
type IpfsDatabase struct {
	// adapter represents an adapter to IPFS and it could be a fake one for testing.
	adapter IpfsAdapter
	// rwlock is a read-write lock for avoiding race condition.
	rwlock sync.RWMutex
}

// NewIpfsDB creates a new IpfsDatabase instance with given url which is the IPFS node's API url.
func NewIpfsDB(url string) *IpfsDatabase {
	s := shell.NewShell(url)
	// In our case, the retrieving of data from IPFS should be fast, otherwise we regard it as 'not exist'.
	s.SetTimeout(ipfsTimeout * time.Second)
	return NewIpfsDbWithAdapter(IpfsAdapter(s))
}

// NewIpfsDbWithAdapter creates a new IpfsDatabase instance with given IPFS adapter.
func NewIpfsDbWithAdapter(adapter IpfsAdapter) *IpfsDatabase {
	return &IpfsDatabase{
		adapter: adapter,
	}
}

// Get retrieves data from IPFS with given key.
func (db *IpfsDatabase) Get(key []byte) ([]byte, error) {
	db.rwlock.RLock()
	defer db.rwlock.RUnlock()

	k := string(key[:])
	reader, err := db.adapter.Cat(k)
	if err != nil {
		return nil, err
	}
	defer reader.Close()

	return ioutil.ReadAll(reader)
}

// Put saves data to IPFS and return key(internally it is a hash).
func (db *IpfsDatabase) Put(value []byte) ([]byte, error) {
	reader := bytes.NewBuffer(value)

	db.rwlock.Lock()
	defer db.rwlock.Unlock()

	// Automatically pin the added data in IPFS.
	hash, err := db.adapter.Add(reader)

	if err != nil {
		return nil, err
	} else {
		return []byte(hash), nil
	}
}

// Discard data from IPFS network.
func (db *IpfsDatabase) Discard(key []byte) error {
	db.rwlock.Lock()
	defer db.rwlock.Unlock()

	k := string(key[:])
	return db.adapter.Unpin(k)
}

// Has checks if the data specified by given key can be retrieved.
func (db *IpfsDatabase) Has(key []byte) bool {
	_, err := db.Get(key)
	// We regard the case where the data cannot be retrieved as "not exist"
	return err == nil
}

// FakeIpfsAdapter is a fake IPFS for unit test.
type FakeIpfsAdapter struct {
	store map[string][]byte
}

// NewFakeIpfsAdapter creates a new FakeIpfsAdapter instance.
func NewFakeIpfsAdapter() *FakeIpfsAdapter {
	return &FakeIpfsAdapter{
		store: map[string][]byte{},
	}
}

func (adapter *FakeIpfsAdapter) Cat(path string) (io.ReadCloser, error) {
	buf := adapter.store[path]
	if buf == nil {
		return nil, errors.New("Path not found.")
	}
	return ioutil.NopCloser(bytes.NewReader(buf)), nil
}

func (adapter *FakeIpfsAdapter) Add(r io.Reader) (string, error) {
	data, _ := ioutil.ReadAll(r)
	hash := sha256.Sum256(data)
	path := hexutil.Encode(hash[:])
	adapter.store[path] = data[:]
	return path, nil
}

func (adapter *FakeIpfsAdapter) Unpin(path string) error {
	delete(adapter.store, path)
	return nil
}
