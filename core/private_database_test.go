package core

import (
	"bytes"
	"reflect"
	"testing"

	"fmt"

	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/core/types"
	"bitbucket.org/cpchain/chain/crypto/sha3"
	"bitbucket.org/cpchain/chain/ethdb"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/ethereum/go-ethereum/trie"
	"github.com/pkg/errors"
)

func TestGetPrivateStateRoot(t *testing.T) {
	db := ethdb.NewMemDatabase()
	blockRoot := common.BytesToHash([]byte{1, 2, 3, 4, 5, 6, 7, 8})
	privateRoot := common.BytesToHash([]byte{1, 2, 3, 4, 5, 6, 7, 8})

	WritePrivateStateRoot(db, blockRoot, privateRoot)

	type args struct {
		db        ethdb.Database
		blockRoot common.Hash
	}
	tests := []struct {
		name string
		args args
		want common.Hash
	}{
		{
			name: "Positive Case: get private state root",
			args: args{
				db:        db,
				blockRoot: blockRoot,
			},
			want: privateRoot,
		},
		{
			name: "Get private state root which does not exist ",
			args: args{
				db:        db,
				blockRoot: common.Hash{},
			},
			want: common.Hash{},
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := GetPrivateStateRoot(tt.args.db, tt.args.blockRoot); !reflect.DeepEqual(got, tt.want) {
				t.Errorf("GetPrivateStateRoot() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestWritePrivateStateRoot(t *testing.T) {
	db := ethdb.NewMemDatabase()
	blockRoot := common.BytesToHash([]byte{1, 2, 3, 4, 5, 6, 7, 8})
	privateRoot := common.BytesToHash([]byte{1, 2, 3, 4, 5, 6, 7, 8})

	type args struct {
		db        ethdb.Database
		blockRoot common.Hash
		root      common.Hash
	}
	tests := []struct {
		name    string
		args    args
		wantErr bool
	}{
		{
			name: "Positive Case: write a private state root",
			args: args{
				db:        db,
				blockRoot: blockRoot,
				root:      privateRoot,
			},
			wantErr: false,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if err := WritePrivateStateRoot(tt.args.db, tt.args.blockRoot, tt.args.root); (err != nil) != tt.wantErr {
				t.Errorf("WritePrivateStateRoot() error = %v, wantErr %v", err, tt.wantErr)
			}
		})
	}
}

func TestWritePrivateReceipt(t *testing.T) {
	type args struct {
		receipt *types.Receipt
		txHash  common.Hash
		db      *trie.Database
	}

	db := getTestTrieDB()
	receipt := getTestReceipt()

	tests := []struct {
		name    string
		args    args
		wantErr bool
		check   func() error
	}{
		{
			name: "Write a normal receipt to normal database",
			args: args{
				receipt: receipt,
				txHash:  common.Hash{},
				db:      db,
			},
			wantErr: false,
			check: func() error {
				nodes := db.Nodes()
				if len(nodes) == 0 {
					return errors.New("No data is written into db.")
				}

				contentToHash := bytes.Join([][]byte{
					privateReceiptPrefix,
					common.Hash{}.Bytes(),
				}, []byte{})
				hasher := sha3.NewKeccak256()
				hasher.Write(contentToHash)
				hashBytes := hasher.Sum(nil)
				hash := common.BytesToHash(hashBytes)

				content, err := db.Node(hash)
				if err != nil || len(content) == 0 {
					return errors.New("The data written has wrong hash and content.")
				}
				return nil
			},
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if err := WritePrivateReceipt(tt.args.receipt, tt.args.txHash, tt.args.db); (err != nil) != tt.wantErr {
				t.Errorf("WritePrivateReceipt() error = %v, wantErr %v", err, tt.wantErr)
			}
			if tt.check != nil {
				if err := tt.check(); err != nil {
					t.Errorf("Checking the result fails for test case <%s>, error is %s", tt.name, err.Error())
				}
			}
		})
	}
}

func TestReadPrivateReceipt(t *testing.T) {
	type args struct {
		txHash common.Hash
		db     *trie.Database
	}

	db := getTestTrieDB()
	receipt := getTestReceipt()

	WritePrivateReceipt(receipt, common.Hash{}, db)
	r, _ := ReadPrivateReceipt(common.Hash{}, db)
	fmt.Println(r)

	tests := []struct {
		name    string
		args    args
		want    *types.Receipt
		wantErr bool
	}{
		{
			name: "Read private transaction receipt",
			args: args{
				txHash: common.Hash{},
				db:     db,
			},
			want:    receipt,
			wantErr: false,
		},
		{
			name: "Read a non-existed private transaction receipt",
			args: args{
				txHash: common.BytesToHash([]byte{1, 1, 1, 1, 1, 1, 1, 1}),
				db:     db,
			},
			want:    nil,
			wantErr: true,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := ReadPrivateReceipt(tt.args.txHash, tt.args.db)
			if (err != nil) != tt.wantErr {
				t.Errorf("ReadPrivateReceipt() error = %v, wantErr %v", err, tt.wantErr)
				return
			}

			var gotBytes, wantBytes []byte
			if got != nil {
				gotBytes, err = rlp.EncodeToBytes(got)

			}
			if tt.want != nil {
				wantBytes, err = rlp.EncodeToBytes(tt.want)
			}
			if !reflect.DeepEqual(gotBytes, wantBytes) {
				t.Errorf("ReadPrivateReceipt() = %v, want %v", got, tt.want)
			}
		})
	}
}

func getTestReceipt() *types.Receipt {
	return types.NewReceipt(common.Hash{}.Bytes(), false, 3000)
}

func getTestTrieDB() *trie.Database {
	return trie.NewDatabase(ethdb.NewMemDatabase())
}
