// +build !race

// Copyright 2016 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package core

import (
	"math/big"
	"math/rand"
	"reflect"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

// Tests that transactions can be added to strict lists and list contents and
// nonce boundaries are correctly maintained.
func TestStrictTxListAdd(t *testing.T) {
	// Generate a list of transactions to insert
	key, _ := crypto.GenerateKey()

	txs := make(types.Transactions, 1024)
	for i := 0; i < len(txs); i++ {
		txs[i] = transaction(uint64(i), 0, key)
	}
	// Insert the transactions in a random order
	list := newTxList(true)
	for _, v := range rand.Perm(len(txs)) {
		list.Add(txs[v], DefaultTxPoolConfig.PriceBump)
	}
	// Verify internal state
	if len(list.txs.items) != len(txs) {
		t.Errorf("transaction count mismatch: have %d, want %d", len(list.txs.items), len(txs))
	}
	for i, tx := range txs {
		if list.txs.items[tx.Nonce()].Tx() != tx {
			t.Errorf("item %d: transaction mismatch: have %v, want %v", i, list.txs.items[tx.Nonce()], tx)
		}
	}
}

func generateTxSortedMap(baseTime time.Time) *txSortedMap {
	size := 20
	items := make(map[uint64]*TimedTransaction)
	index := make(nonceHeap, size)

	for i := uint64(0); i < uint64(size); i++ {
		items[i] = &TimedTransaction{
			Transaction: types.NewTransaction(i, common.Address{}, big.NewInt(0), uint64(0), big.NewInt(0), []byte{}),
			updateTime:  baseTime,
		}
		index = append(index, i)
		baseTime = baseTime.Add(time.Second * 10)
	}

	return &txSortedMap{
		items: items,
		index: &index,
	}
}

func Test_txSortedMap_AllBefore(t *testing.T) {
	type fields struct {
		items map[uint64]*TimedTransaction
		index *nonceHeap
		cache types.Transactions
	}
	type args struct {
		t time.Time
	}

	baseTime, _ := time.Parse(time.RFC3339, "2019-01-01T00:00:00+00:00")
	fakeTxSortedMap := generateTxSortedMap(baseTime)
	argTime := baseTime.Add(time.Minute * 1)
	wantResult := func() []types.Transactions {
		var results []types.Transactions
		var result []*types.Transaction
		for i := 0; i < 6; i++ {
			result = append(
				result,
				types.NewTransaction(uint64(i), common.Address{}, big.NewInt(0), uint64(0), big.NewInt(0), []byte{}),
			)
		}
		results = append(results, result)
		return results
	}()

	tests := []struct {
		name        string
		fields      fields
		args        args
		wantResults []types.Transactions
	}{
		// TODO: Add test cases.
		{
			"test1",
			fields{
				fakeTxSortedMap.items,
				fakeTxSortedMap.index,
				fakeTxSortedMap.cache,
			},
			args{
				argTime,
			},
			wantResult,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			m := &txSortedMap{
				items: tt.fields.items,
				index: tt.fields.index,
				cache: tt.fields.cache,
			}
			if gotResults := m.AllBefore(tt.args.t); !reflect.DeepEqual(gotResults, tt.wantResults) {
				t.Errorf("txSortedMap.AllBefore() = %v, want %v", gotResults, tt.wantResults)
			}
		})
	}
}
