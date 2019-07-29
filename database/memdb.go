// Copyright 2018 The cpchain authors
// Copyright 2014 The go-ethereum Authors

package database

import (
	"errors"
	"sync"

	"github.com/ethereum/go-ethereum/common"
)

var ErrKeyNotFound = errors.New("not found")

type MemDatabase struct {
	db map[string][]byte
	rw sync.RWMutex
}

func NewMemDatabase() *MemDatabase {
	return &MemDatabase{
		db: make(map[string][]byte),
	}
}

func (db *MemDatabase) Put(key []byte, value []byte) error {
	db.rw.Lock()
	defer db.rw.Unlock()

	db.db[string(key)] = common.CopyBytes(value)
	return nil
}

func (db *MemDatabase) Has(key []byte) (bool, error) {
	db.rw.RLock()
	defer db.rw.RUnlock()

	_, ok := db.db[string(key)]
	return ok, nil
}

func (db *MemDatabase) Get(key []byte) ([]byte, error) {
	db.rw.RLock()
	defer db.rw.RUnlock()

	if entry, ok := db.db[string(key)]; ok {
		return common.CopyBytes(entry), nil
	}
	return nil, ErrKeyNotFound
}

func (db *MemDatabase) Keys() [][]byte {
	db.rw.RLock()
	defer db.rw.RUnlock()

	var keys [][]byte
	for key := range db.db {
		keys = append(keys, []byte(key))
	}
	return keys
}

func (db *MemDatabase) Delete(key []byte) error {
	db.rw.Lock()
	defer db.rw.Unlock()

	delete(db.db, string(key))
	return nil
}

func (db *MemDatabase) Close() {}

func (db *MemDatabase) NewBatch() Batch {
	return &memBatch{db: db}
}

func (db *MemDatabase) Len() int {
	db.rw.RLock()
	defer db.rw.RUnlock()

	return len(db.db)
}

type kv struct{ k, v []byte }

type memBatch struct {
	db     *MemDatabase
	writes []kv
	size   int // for ValueSize
	rw     sync.RWMutex
}

func (b *memBatch) Put(key, value []byte) error {
	b.rw.Lock()
	defer b.rw.Unlock()

	b.writes = append(b.writes, kv{common.CopyBytes(key), common.CopyBytes(value)})
	b.size += len(value)
	return nil
}

func (b *memBatch) Delete(key []byte) error {
	b.rw.Lock()
	defer b.rw.Unlock()

	b.writes = append(b.writes, kv{common.CopyBytes(key), nil})
	b.size++
	return nil
}

func (b *memBatch) Write() error {
	b.rw.Lock()
	defer b.rw.Unlock()

	b.db.rw.Lock()
	defer b.db.rw.Unlock()

	for _, kv := range b.writes {
		if kv.v == nil {
			delete(b.db.db, string(kv.k))
			continue
		}
		b.db.db[string(kv.k)] = kv.v
	}
	return nil
}

func (b *memBatch) ValueSize() int {
	b.rw.RLock()
	defer b.rw.RUnlock()

	return b.size
}

func (b *memBatch) Reset() {
	b.rw.Lock()
	defer b.rw.Unlock()

	b.writes = b.writes[:0]
	b.size = 0
}
