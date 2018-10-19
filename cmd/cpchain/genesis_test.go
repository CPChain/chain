// Copyright 2016 The go-ethereum Authors
// This file is part of go-ethereum.
//
// go-ethereum is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// go-ethereum is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with go-ethereum. If not, see <http://www.gnu.org/licenses/>.

package main

import (
	"io/ioutil"
	"os"
	"path/filepath"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/core/rawdb"
	"bitbucket.org/cpchain/chain/ethdb"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
)

var customGenesisTests = []struct {
	genesis string
	query   string
	result  string
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
		`,
		query:  "eth.getBlock(0).nonce",
		result: "0x0000000000000042",
	},
	// Genesis file with an empty chain configuration (ensure missing fields work)
	{
		genesis: `
			coinbase    = "0x0000000000000000000000000000000000000000"
			difficulty  = "0x20000"
			extraData   = ""
			gasLimit    = "0x2fefd8"
			nonce       = "0x0000000000000042"
			mixhash     = "0x0000000000000000000000000000000000000000000000000000000000000000"
			parentHash  = "0x0000000000000000000000000000000000000000000000000000000000000000"
			timestamp   = "0x00"
		`,
		query:  "eth.getBlock(0).nonce",
		result: "0x0000000000000042",
	},
	// Genesis file with specific chain configurations
	{
		genesis: `
			coinbase    = "0x0000000000000000000000000000000000000000"
			difficulty  = "0x20000"
			extraData   = ""
			gasLimit    = "0x2fefd8"
			nonce       = "0x0000000000000042"
			mixhash     = "0x0000000000000000000000000000000000000000000000000000000000000000"
			parentHash  = "0x0000000000000000000000000000000000000000000000000000000000000000"
			timestamp   = "0x00"
            [config]
				homesteadBlock  = 314
				daoForkBlock    = 141
				daoForkSupport  = true
		`,
		query:  "eth.getBlock(0).nonce",
		result: "0x0000000000000042",
	},
}

// Tests that initializing Geth with a custom genesis block and chain definitions
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
		checkGenesisNonceHex(t, datadir, tt.result)
	}
}

func checkGenesisNonceHex(t *testing.T, datadir string, nonceHex string) {
	dbPath := filepath.Join(datadir, configs.DatabaseName)
	db, _ := ethdb.NewLDBDatabase(dbPath, 0, 0)
	number := uint64(0)
	hash := rawdb.ReadCanonicalHash(db, number)
	if hash == (common.Hash{}) {
		t.Fatal("Genesis block is missing.")
	}

	block := rawdb.ReadBlock(db, hash, number)
	if block != nil {
		gotNonceHex := hexutil.EncodeUint64(block.Nonce())
		if gotNonceHex != nonceHex {
			t.Errorf("Genesis block is not expected. Want %v, Got %v", nonceHex, gotNonceHex)
		}
	} else {
		t.Fatal("Genesis block is missing.")
	}
	return
}
