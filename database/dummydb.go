// Copyright 2019 The cpchain authors

package database

// DummyDatabase is a dummy "remote database" which actually save all data to key, i.e. key is data, data is key.
// It does not save data to any store, but to the returned key. It is used to serve as an extremely stable remote database.
// For example, PrivateTx could use it as an option of its "remote database" to ensure that it does not depend on any "single point" database.
type DummyDatabase struct {
}

func (d *DummyDatabase) Get(key []byte) ([]byte, error) {
	return key, nil
}

func (d *DummyDatabase) Put(value []byte) ([]byte, error) {
	return value, nil
}

func (d *DummyDatabase) Discard(key []byte) error {
	// don't need to do anything
	return nil
}

func (d *DummyDatabase) Has(key []byte) bool {
	return true
}
