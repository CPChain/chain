package core

import (
	"reflect"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/ethdb"
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
