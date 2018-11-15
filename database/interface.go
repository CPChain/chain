// Copyright 2018 The cpchain authors
// Copyright 2014 The go-ethereum Authors

package database

// Code using batches should try to add this much data to the batch.
// The value was determined empirically.
const IdealBatchSize = 100 * 1024

// Putter wraps the database write operation supported by both batches and regular databases.
type Putter interface {
	Put(key []byte, value []byte) error
}

// Deleter wraps the database delete operation supported by both batches and regular databases.
type Deleter interface {
	Delete(key []byte) error
}

// Database wraps all database operations. All methods are safe for concurrent use.
type Database interface {
	Putter
	Deleter
	Get(key []byte) ([]byte, error)
	Has(key []byte) (bool, error)
	Close()
	NewBatch() Batch
}

// Batch is a write-only database that commits changes to its host database
// when Write is called. Batch cannot be used concurrently.
type Batch interface {
	Putter
	Deleter
	ValueSize() int // amount of data in the batch
	Write() error
	// Reset resets the batch for reuse
	Reset()
}

// RemoteDatabase represents the database interface that be able to maintain a huge amount of data. Distributed p2p database
// such as ipfs is the classic implementation of the interface.
type RemoteDatabase interface {
	// Get gets data from database with given key.
	Get(key []byte) ([]byte, error)
	// Put puts data to database and returns an address(key/identifier).
	Put(value []byte) ([]byte, error)
	// Discard discards data from database with given key. As remote database system such as IPFS doesn't have explicit
	// data deleting function as its own implementation mechanism, we adopt 'discard' instead of 'delete'.
	Discard(key []byte) error
	// Has checks if the given address/key points to an existent data.
	Has(key []byte) bool
}
