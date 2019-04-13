// Copyright 2017 The go-ethereum Authors
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
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/core/rawdb"
	"bitbucket.org/cpchain/chain/database"
	"github.com/davecgh/go-spew/spew"
	"github.com/ethereum/go-ethereum/common"
)

func TestDefaultGenesisBlock(t *testing.T) {
	runmode := configs.GetRunMode()
	configs.SetRunMode(configs.Mainnet)
	block := DefaultGenesisBlock().ToBlock(nil)
	if block.Hash() != MainnetGenesisHash {
		t.Errorf("wrong mainnet genesis hash, got %v, want %v", block.Hash().Hex(), MainnetGenesisHash.Hex())
	}
	configs.SetRunMode(runmode)
}

func TestSetupGenesis(t *testing.T) {
	runmode := configs.GetRunMode()
	configs.SetRunMode(configs.Mainnet)
	var (
		customghash = common.HexToHash("0x7665f953c35e95322ebc826f0293500e3bf00689f1f9565be0b7cd097897988d")
		customg     = Genesis{
			Config: &configs.ChainConfig{},
			Alloc: GenesisAlloc{
				{1}: {Balance: big.NewInt(1), Storage: map[common.Hash]common.Hash{{1}: {1}}},
			},
		}
		oldcustomg = customg
	)
	oldcustomg.Config = &configs.ChainConfig{}
	tests := []struct {
		name       string
		fn         func(database.Database) (*configs.ChainConfig, common.Hash, error)
		wantConfig *configs.ChainConfig
		wantHash   common.Hash
		wantErr    error
	}{
		{
			name: "genesis without ChainConfig",
			fn: func(db database.Database) (*configs.ChainConfig, common.Hash, error) {
				return SetupGenesisBlock(db, new(Genesis))
			},
			wantErr:    errGenesisNoConfig,
			wantConfig: configs.ChainConfigInfo(),
		},
		{
			name: "no block in DB, genesis == nil",
			fn: func(db database.Database) (*configs.ChainConfig, common.Hash, error) {
				return SetupGenesisBlock(db, nil)
			},
			wantHash:   MainnetGenesisHash,
			wantConfig: configs.ChainConfigInfo(),
		},
		{
			name: "mainnet block in DB, genesis == nil",
			fn: func(db database.Database) (*configs.ChainConfig, common.Hash, error) {
				DefaultGenesisBlock().MustCommit(db)
				return SetupGenesisBlock(db, nil)
			},
			wantHash:   MainnetGenesisHash,
			wantConfig: configs.ChainConfigInfo(),
		},
		{
			name: "custom block in DB, genesis == nil",
			fn: func(db database.Database) (*configs.ChainConfig, common.Hash, error) {
				customg.MustCommit(db)
				return SetupGenesisBlock(db, nil)
			},
			wantHash:   customghash,
			wantConfig: customg.Config,
		},
		{
			name: "compatible config in DB",
			fn: func(db database.Database) (*configs.ChainConfig, common.Hash, error) {
				oldcustomg.MustCommit(db)
				return SetupGenesisBlock(db, &customg)
			},
			wantHash:   customghash,
			wantConfig: customg.Config,
		},
	}

	for _, test := range tests {
		db := database.NewMemDatabase()
		config, hash, err := test.fn(db)
		// Check the return values.
		if !reflect.DeepEqual(err, test.wantErr) {
			spew := spew.ConfigState{DisablePointerAddresses: true, DisableCapacities: true}
			t.Errorf("%s: returned error %#v, want %#v", test.name, spew.NewFormatter(err), spew.NewFormatter(test.wantErr))
		}
		if !reflect.DeepEqual(config, test.wantConfig) {
			t.Errorf("%s:\nreturned %v\nwant     %v", test.name, config, test.wantConfig)
		}
		if hash != test.wantHash {
			t.Errorf("%s: returned hash %s, want %s", test.name, hash.Hex(), test.wantHash.Hex())
		} else if err == nil {
			// Check database content.
			stored := rawdb.ReadBlock(db, test.wantHash, 0)
			if stored.Hash() != test.wantHash {
				t.Errorf("%s: block in DB has hash %s, want %s", test.name, stored.Hash(), test.wantHash)
			}
		}
	}
	configs.SetRunMode(runmode)
}
