package dpor

import (
	"fmt"
	"math/big"
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/hashicorp/golang-lru"
	"github.com/stretchr/testify/assert"
)

func TestDpor_VerifyHeader(t *testing.T) {

	tests := []struct {
		name          string
		verifySuccess bool
		wantErr       bool
	}{
		{"verifyHeader success", true, false},
		{"verifyHeader failed", false, true},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				dh: &fakeDporHelper{verifySuccess: tt.verifySuccess},
			}

			err := c.VerifyHeader(&FakeReader{}, newHeader(), true, newHeader())
			fmt.Println("err:", err)
			if err := c.VerifyHeader(&FakeReader{}, newHeader(), true, newHeader()); (err != nil) != tt.wantErr {
				t.Errorf("Dpor.VerifyHeaders() got = %v, want %v", err, tt.wantErr)
			}
		})
	}
}

func TestDpor_VerifyHeaders(t *testing.T) {
	tests := []struct {
		name          string
		verifySuccess bool
		wantErr       bool
	}{
		{"verifyHeader success", true, true},
		{"verifyHeader failed", false, false},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				dh: &fakeDporHelper{verifySuccess: tt.verifySuccess},
			}
			_, results := c.VerifyHeaders(
				&FakeReader{},
				[]*types.Header{newHeader()},
				[]bool{true},
				[]*types.Header{newHeader()})

			got := <-results
			fmt.Println("got:", got)
			if tt.wantErr != (got == nil) {
				t.Errorf("Dpor.VerifyHeaders() got = %v, want %v", got, tt.wantErr)
			}
		})
	}
}

func TestDpor_APIs(t *testing.T) {
	c := &Dpor{
		dh: &fakeDporHelper{},
	}
	got := c.APIs(nil)
	assert.Equal(t, 1, len(got), "only 1 api should be created")
}

// ========================================================

func TestDpor_Prepare(t *testing.T) {
	type fields struct {
		config       *configs.DporConfig
		db           database.Database
		recents      *lru.ARCCache
		signatures   *lru.ARCCache
		signedBlocks map[uint64]common.Hash
		signer       common.Address
		signFn       SignerFn
	}
	type args struct {
		chain  consensus.ChainReader
		header *types.Header
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				config:       tt.fields.config,
				db:           tt.fields.db,
				recents:      tt.fields.recents,
				signatures:   tt.fields.signatures,
				signedBlocks: tt.fields.signedBlocks,
				signer:       tt.fields.signer,
				signFn:       tt.fields.signFn,
			}
			if err := c.PrepareBlock(tt.args.chain, tt.args.header); (err != nil) != tt.wantErr {
				t.Errorf("Dpor.Prepare(%v, %v) error = %v, wantErr %v", tt.args.chain, tt.args.header, err, tt.wantErr)
			}
		})
	}
}

func TestDpor_Seal(t *testing.T) {
	type fields struct {
		config       *configs.DporConfig
		db           database.Database
		recents      *lru.ARCCache
		signatures   *lru.ARCCache
		signedBlocks map[uint64]common.Hash
		signer       common.Address
		signFn       SignerFn
		// lock         sync.RWMutex
	}
	type args struct {
		chain consensus.ChainReader
		block *types.Block
		stop  <-chan struct{}
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		want    *types.Block
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				config:       tt.fields.config,
				db:           tt.fields.db,
				recents:      tt.fields.recents,
				signatures:   tt.fields.signatures,
				signedBlocks: tt.fields.signedBlocks,
				signer:       tt.fields.signer,
				signFn:       tt.fields.signFn,
				// lock:         tt.fields.lock,
			}
			got, err := c.Seal(tt.args.chain, tt.args.block, tt.args.stop)
			if (err != nil) != tt.wantErr {
				t.Errorf("Dpor.Seal(%v, %v, %v) error = %v, wantErr %v", tt.args.chain, tt.args.block, tt.args.stop, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("Dpor.Seal(%v, %v, %v) = %v, want %v", tt.args.chain, tt.args.block, tt.args.stop, got, tt.want)
			}
		})
	}
}

func TestDpor_CalcDifficulty(t *testing.T) {
	tests := []struct {
		name            string
		verifySuccess   bool
		snapshotSuccess bool
		want            *big.Int
	}{
		{"verifyHeader success", true, true, big.NewInt(10)},
		{"verifyHeader success", false, false, nil},
		{"verifyHeader failed", false, true, nil},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			c := &Dpor{
				dh:     &fakeDporHelper{verifySuccess: tt.verifySuccess, snapshotSuccess: tt.snapshotSuccess, dporUtil: &fakeDporUtil{success: tt.verifySuccess}},
				signer: addr1,
			}

			got := c.CalcDifficulty(&FakeReader{}, 0, newHeader())
			fmt.Println("got:", got)
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("Dpor.CalcDifficulty() got = %v, want %v", got, tt.want)
			}
		})
	}
}
