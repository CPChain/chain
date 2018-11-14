// Copyright 2016 The go-ethereum Authors

package main

import (
	"io/ioutil"
	"os"
	"path/filepath"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/core/rawdb"
	"bitbucket.org/cpchain/chain/database"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
)

var customGenesisTests = []struct {
	genesis string
	result  string
	success bool
}{
	// Plain genesis file without anything extra
	{
		genesis: `
			coinbase    = "0x0000000000000000000000000000000000000000"
			difficulty  = "0x20000"
			extraData   = ""
			gasLimit    = "0x2fefd8"
			nonce       = "0x0000000000000042"
			mixHash     = "0x0000000000000000000000000000000000000000000000000000000000000000"
			parentHash  = "0x0000000000000000000000000000000000000000000000000000000000000000"
			timestamp   = "0x00"
			[alloc]
`,
		success: false,
		result:  "",
	},
	// Genesis file with an empty chain configuration (ensure missing fields work)
	{
		genesis: `
			coinbase    = "0x0000000000000000000000000000000000000000"
			difficulty  = "0x20000"
			extraData   = ""
			gasLimit    = "0x2fefd8"
			nonce       = "0x0000000000000042"
			mixHash     = "0x0000000000000000000000000000000000000000000000000000000000000000"
			parentHash  = "0x0000000000000000000000000000000000000000000000000000000000000000"
			timestamp   = "0x00"
            [alloc]
            [config]
		`,
		success: true,
		result:  "0x42",
	},
	// Genesis file with specific chain configurations
	{
		genesis: `
			coinbase    = "0x0000000000000000000000000000000000000000"
			difficulty  = "0x20000"
			extraData   = ""
			gasLimit    = "0x2fefd8"
			nonce       = "0x0000000000000042"
			mixHash     = "0x0000000000000000000000000000000000000000000000000000000000000000"
			parentHash  = "0x0000000000000000000000000000000000000000000000000000000000000000"
			timestamp   = "0x00"
	       [config]
           [alloc]
		`,
		success: true,
		result:  "0x42",
	},
}

// Tests that initializing cpchain with a custom genesis block and chain definitions
// work properly.
func TestCustomGenesis(t *testing.T) {
	for i, tt := range customGenesisTests {
		// Create a temporary data directory to use and inspect later
		datadir := tmpdir(t)
		defer os.RemoveAll(datadir)

		// Initialize the data directory with the custom genesis block
		toml := filepath.Join(datadir, "genesis.toml")
		if err := ioutil.WriteFile(toml, []byte(tt.genesis), 0600); err != nil {
			t.Fatalf("test %d: failed to write genesis file: %v", i, err)
		}
		runCpchain(t, "chain", "init", toml, "--datadir", datadir).WaitExit()

		// Check result
		checkGenesisNonceHex(t, datadir, tt.result, tt.success)
	}
}

func checkGenesisNonceHex(t *testing.T, datadir string, nonceHex string, wantSuccess bool) {
	dbPath := filepath.Join(datadir, "/cpchain/"+configs.DatabaseName)
	db, _ := database.NewLDBDatabase(dbPath, 0, 0)
	number := uint64(0)
	hash := rawdb.ReadCanonicalHash(db, number)
	if hash == (common.Hash{}) {
		if wantSuccess {
			t.Fatal("Genesis block is missing.")
		} else {
			// Expect fail
			return
		}
	} else {
		if !wantSuccess {
			t.Error("Want to fail to create genesis block, but the genesis block has been created successfully.")
		}
	}

	block := rawdb.ReadBlock(db, hash, number)
	if block != nil {
		wantNonce, _ := hexutil.DecodeUint64(nonceHex)

		if block.Nonce() != wantNonce {
			t.Errorf("Genesis block is not expected. Want %v, Got %v", wantNonce, block.Nonce())
		}
	} else {
		t.Fatal("Genesis block is missing.")
	}
	return
}
