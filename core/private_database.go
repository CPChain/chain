package core

import (
	"bytes"
	"fmt"

	"bitbucket.org/cpchain/chain/crypto/sha3"
	"bitbucket.org/cpchain/chain/ethdb"
	"bitbucket.org/cpchain/chain/types"

	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
)

var (
	privateRootPrefix    = []byte("Priv")
	privateReceiptPrefix = []byte("PrivR")
)

// GetPrivateStateRoot gets the root(hash) for private state associated with the root of Merkle tree in public chain.
func GetPrivateStateRoot(db ethdb.Database, blockRoot common.Hash) common.Hash {
	exist, _ := db.Has(append(privateRootPrefix, blockRoot[:]...))
	if exist {
		root, _ := db.Get(append(privateRootPrefix, blockRoot[:]...))
		return common.BytesToHash(root)
	}
	return common.Hash{}
}

// WritePrivateStateRoot writes the root(hash) for private state associated with the root of Merkle tree in public chain.
func WritePrivateStateRoot(db ethdb.Database, blockRoot, root common.Hash) error {
	return db.Put(append(privateRootPrefix, blockRoot[:]...), root[:])
}

// WritePrivateReceipt writes private receipt associated with specified transaction.
func WritePrivateReceipt(receipt *types.Receipt, txHash common.Hash, db ethdb.Database) error {
	hash := getPrivateReceiptKey(txHash)
	// Write receipt to trie db.
	storageReceipt := (*types.ReceiptForStorage)(receipt)
	bytesToWrite, _ := rlp.EncodeToBytes(storageReceipt)
	db.Put(hash.Bytes(), bytesToWrite)
	log.Info("Write private transaction receipt", "hash", hash.String(), "receipt", fmt.Sprintf("%+v", receipt))
	return nil
}

// ReadPrivateReceipt reads private receipt associated with specified transaction.
func ReadPrivateReceipt(txHash common.Hash, db ethdb.Database) (*types.Receipt, error) {
	hash := getPrivateReceiptKey(txHash)
	// Read private receipt data
	data, err := db.Get(hash.Bytes())
	if err != nil {
		return nil, err
	}
	// Decode receipt
	storageReceipt := types.ReceiptForStorage{}
	rlp.DecodeBytes(data, &storageReceipt)
	receipt := (*types.Receipt)(&storageReceipt)
	// TODO: workaround for a suspected bug on RLP of Receipt.
	if len(receipt.PostState) != 0 {
		receipt.Status = types.ReceiptStatusSuccessful
	}

	return (*types.Receipt)(&storageReceipt), nil
}

func getPrivateReceiptKey(txHash common.Hash) common.Hash {
	// Generate hash combining tx hash and private receipt prefix.
	// It aims at avoiding conflict.
	contentToHash := bytes.Join([][]byte{
		privateReceiptPrefix,
		txHash.Bytes(),
	}, []byte{})
	hasher := sha3.NewKeccak256()
	hasher.Write(contentToHash)
	hashBytes := hasher.Sum(nil)
	return common.BytesToHash(hashBytes)
}
