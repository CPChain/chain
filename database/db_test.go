// Copyright 2018 The go-ethereum Authors
// Copyright 2014 The go-ethereum Authors

package database_test

import (
	"bytes"
	"fmt"
	"strconv"
	"sync"
	"testing"

	"bitbucket.org/cpchain/chain/database"
)

var testValues = []string{"", "a", "1251", "\x00123\x00"}

var testValueSize = func() (size int) {
	for _, v := range testValues {
		size += len(v)
	}
	return
}()

func testDBFuncs(db database.Database, t *testing.T) {
	t.Parallel()

	// put the values
	for _, v := range testValues {
		err := db.Put([]byte(v), []byte(v))
		if err != nil {
			t.Fatalf("put failed: %v\n", err)
		}
	}

	// check if we have the values
	for _, v := range testValues {
		if hasKey, _ := db.Has([]byte(v)); !hasKey {
			t.Fatalf("key not found for: %q", v)
		}
	}

	// get the values
	for _, v := range testValues {
		data, err := db.Get([]byte(v))
		if err != nil {
			t.Fatalf("get failed: %v\n", err)
		}
		if !bytes.Equal(data, []byte(v)) {
			t.Fatalf("get returned wrong result, got %q expected %q\n", string(data), v)
		}
	}

	// override each key with the value "?"
	for _, v := range testValues {
		err := db.Put([]byte(v), []byte("?"))
		if err != nil {
			t.Fatalf("put override failed: %v\n", err)
		}
	}

	// check value
	for _, v := range testValues {
		data, err := db.Get([]byte(v))
		if err != nil {
			t.Fatalf("get failed: %v\n", err)
		}
		if !bytes.Equal(data, []byte("?")) {
			t.Fatalf("get returned wrong result, got %q expected ?\n", string(data))
		}
	}

	// check modification on retrieved values doesn't affect those stored in the db
	for _, v := range testValues {
		orig, err := db.Get([]byte(v))
		if err != nil {
			t.Fatalf("get failed: %v\n", err)
		}
		orig[0] = byte(0xff)
		data, err := db.Get([]byte(v))
		if err != nil {
			t.Fatalf("get failed: %v\n", err)
		}
		if !bytes.Equal(data, []byte("?")) {
			t.Fatalf("get returned wrong result, got %q expected ?\n", string(data))
		}
	}

	// delete the keys
	for _, v := range testValues {
		err := db.Delete([]byte(v))
		if err != nil {
			t.Fatalf("delete %q failed: %v\n", v, err)
		}
	}

	// check keys have been deleted
	for _, v := range testValues {
		_, err := db.Get([]byte(v))
		if err == nil {
			t.Fatalf("got deleted value %q\n", v)
		}
	}
}

func testParallelDBFuncs(db database.Database, t *testing.T) {
	const n = 8
	var pending sync.WaitGroup

	// put
	pending.Add(n)
	for i := 0; i < n; i++ {
		go func(key string) {
			defer pending.Done()
			err := db.Put([]byte(key), []byte("v"+key))
			if err != nil {
				t.Fatal("put failed: " + err.Error())
			}
		}(strconv.Itoa(i))
	}
	pending.Wait()

	// get
	pending.Add(n)
	for i := 0; i < n; i++ {
		go func(key string) {
			defer pending.Done()
			data, err := db.Get([]byte(key))
			if err != nil {
				t.Fatal("get failed: " + err.Error())
			}
			if !bytes.Equal(data, []byte("v"+key)) {
				t.Fatal(fmt.Sprintf("get failed, got %q expected %q", []byte(data), []byte("v"+key)))
			}
		}(strconv.Itoa(i))
	}
	pending.Wait()

	// delete
	pending.Add(n)
	for i := 0; i < n; i++ {
		go func(key string) {
			defer pending.Done()
			err := db.Delete([]byte(key))
			if err != nil {
				t.Fatal("delete failed: " + err.Error())
			}
		}(strconv.Itoa(i))
	}
	pending.Wait()

	// check deletion
	pending.Add(n)
	for i := 0; i < n; i++ {
		go func(key string) {
			defer pending.Done()
			_, err := db.Get([]byte(key))
			if err == nil {
				t.Fatal("get succeeded")
			}
		}(strconv.Itoa(i))
	}
	pending.Wait()
}

func testBatchFuncs(b database.Batch, t *testing.T) {
	t.Parallel()

	// put the values
	for _, v := range testValues {
		err := b.Put([]byte(v), []byte(v))
		if err != nil {
			t.Fatalf("put failed: %v\n", err)
		}
	}
	inc := testValueSize

	if size := b.ValueSize(); size != inc {
		t.Fatalf("wrong value size: %v\n", size)
	}

	// delete the first key
	if err := b.Delete([]byte(testValues[0])); err != nil {
		t.Fatalf("delete failed: %v\n", err)
	}
	inc++

	// write
	if err := b.Write(); err != nil {
		t.Fatalf("write failed: %v\n", err)
	}
	// after write, the size remains the same.
	// why not clear it?
	if size := b.ValueSize(); size != inc {
		t.Fatalf("wrong value size: %v\n", size)
	}

	// delete the keys
	for _, v := range testValues {
		err := b.Delete([]byte(v))
		if err != nil {
			t.Fatalf("delete failed: %v\n", err)
		}
	}
	inc += len(testValues)

	// value size shouldn't change
	if size := b.ValueSize(); size != inc {
		t.Fatalf("wrong value size: %v\n", size)
	}

	// put the values
	for _, v := range testValues {
		err := b.Put([]byte(v), []byte(v))
		if err != nil {
			t.Fatalf("put failed: %v\n", err)
		}
	}
	// reset it.
	b.Reset()
	if size := b.ValueSize(); size != 0 {
		t.Fatalf("wrong value size: %v\n", size)
	}
}
