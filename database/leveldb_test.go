package database_test

import (
	"bytes"
	"io/ioutil"
	"os"
	"testing"

	"bitbucket.org/cpchain/chain/database"
)

func newTestLDB() (*database.LDBDatabase, func()) {
	dirname, err := ioutil.TempDir(os.TempDir(), "cpcdb_test")
	if err != nil {
		panic("failed to create test file: " + err.Error())
	}
	db, err := database.NewLDBDatabase(dirname, 0, 0)
	if err != nil {
		panic("failed to create test database: " + err.Error())
	}

	// check path
	if dirname != db.Path() {
		panic("wrong db path")
	}

	return db, func() {
		db.Close()
		_ = os.RemoveAll(dirname)
	}
}

func TestLDBFuncs(t *testing.T) {
	db, remove := newTestLDB()
	defer remove()
	testDBFuncs(db, t)
}

func TestLDBDatabase_Iterator(t *testing.T) {
	db, remove := newTestLDB()
	defer remove()
	iter := db.NewIterator()

	// test NewIterator
	if err := db.Put([]byte("aaa"), []byte("bbb")); err != nil {
		t.Fatalf("put failed: %v\n", err)
	}
	for iter.Next() {
		key := iter.Key()
		val := iter.Value()
		if !bytes.Equal(key, []byte("aaa")) {
			t.Fatal("key corrupted")
		}
		if !bytes.Equal(val, []byte("bbb")) {
			t.Fatal("value corrupted")
		}
	}
	iter.Release()
	if err := iter.Error(); err != nil {
		t.Fatalf("release failed: %v\n", err)
	}

	// test NewIteratorWithPrefix
	iter = db.NewIteratorWithPrefix([]byte("foobar"))
	// test NewIterator
	if err := db.Put([]byte("aaa"), []byte("bbb")); err != nil {
		t.Fatalf("put failed: %v\n", err)
	}
	for iter.Next() {
		key := iter.Key()
		val := iter.Value()
		if !bytes.Equal(key, []byte("foobaraaa")) {
			t.Fatal("key corrupted")
		}
		if !bytes.Equal(val, []byte("bbb")) {
			t.Fatal("value corrupted")
		}
	}
	iter.Release()
	if err := iter.Error(); err != nil {
		t.Fatalf("release failed: %v\n", err)
	}

}

func TestLDBBatch(t *testing.T) {
	db, remove := newTestLDB()
	defer remove()

	batch := db.NewBatch()
	testBatchFuncs(batch, t)
}

func TestLDBParallelFuncs(t *testing.T) {
	db, remove := newTestLDB()
	defer remove()
	testParallelDBFuncs(db, t)
}

func TestLDBTableFuncs(t *testing.T) {
	db, remove := newTestLDB()
	defer remove()

	tbl := database.NewTable(db, "foobar")
	defer tbl.Close()

	testDBFuncs(tbl, t)

	// we use table to put
	if err := tbl.Put([]byte("kkkk"), []byte("sss")); err != nil {
		t.Fatalf("put failed: %v\n", err)
	}
	// we use db to get
	if val, err := db.Get([]byte("foobarkkkk")); err != nil {
		t.Fatalf("get failed: %v\n", err)
	} else if bytes.Equal(val, []byte("ssss")) {
		t.Fatal("value mismatch")
	}
}

func TestLDBTableParallelFuncs(t *testing.T) {
	db, remove := newTestLDB()
	defer remove()

	tbl := database.NewTable(db, "foobar")
	defer tbl.Close()

	testParallelDBFuncs(tbl, t)
}

func TestLDBTableBatch(t *testing.T) {
	db, remove := newTestLDB()
	defer remove()

	tbl := database.NewTable(db, "foobar")
	defer tbl.Close()

	batch := tbl.NewBatch()
	testBatchFuncs(batch, t)
}

func TestLDBMisc(t *testing.T) {
	db, remove := newTestLDB()
	defer remove()

	_ = db.LDB()
}
