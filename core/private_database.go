package core

import (
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/ethdb"
)

var (
	privateRootPrefix = []byte("Priv")
	// Blow constants will be used later, I put it here for reminder.
	//privateBlockReceiptsPrefix = []byte("PrivBR")
	//privateReceiptPrefix       = []byte("PrivR")
	//privateBloomPrefix         = []byte("PrivB")
)

func GetPrivateStateRoot(db ethdb.Database, blockRoot common.Hash) common.Hash {
	root, _ := db.Get(append(privateRootPrefix, blockRoot[:]...))
	return common.BytesToHash(root)
}

func WritePrivateStateRoot(db ethdb.Database, blockRoot, root common.Hash) error {
	return db.Put(append(privateRootPrefix, blockRoot[:]...), root[:])
}
