package database_test

import (
	"reflect"
	"sort"
	"testing"

	"bitbucket.org/cpchain/chain/database"
)

func TestMemDatabaseFuncs(t *testing.T) {
	db := database.NewMemDatabase()
	defer db.Close()
	testDBFuncs(db, t)

}

func TestMemDatabase_Keys(t *testing.T) {
	db := database.NewMemDatabase()
	for _, v := range testValues {
		err := db.Put([]byte(v), []byte(v))
		if err != nil {
			t.Fatalf("put failed: %v\n", err)
		}
	}

	keys := db.Keys()
	var keystrs []string
	for _, k := range keys {
		keystrs = append(keystrs, string(k))
	}
	sort.Strings(keystrs)

	strs := append([]string{}, testValues...)
	sort.Strings(strs)
	if eq := reflect.DeepEqual(keystrs, strs); !eq {
		t.Fatal("keys have been altered.")
	}
}

func TestMemDatabase_Len(t *testing.T) {
	db := database.NewMemDatabase()
	for _, v := range testValues {
		err := db.Put([]byte(v), []byte(v))
		if err != nil {
			t.Fatalf("put failed: %v\n", err)
		}
	}
	if dbLen := db.Len(); dbLen != len(testValues) {
		t.Fatal("db length mismatch")
	}
}

func TestMemBatch(t *testing.T) {
	batch := database.NewMemDatabase().NewBatch()
	testBatchFuncs(batch, t)
}

func TestMemDatabaseParallelFuncs(t *testing.T) {
	testParallelDBFuncs(database.NewMemDatabase(), t)
}
