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
	"encoding/json"
	"fmt"
	"os"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"github.com/naoina/toml"
)

func TestDefaultGenesisBlock_MarshalTOML(t *testing.T) {
	genesisblock := DefaultGenesisBlock()
	fmt.Println("==============toml=====================")
	err := toml.NewEncoder(os.Stdout).Encode(genesisblock)
	if err != nil {
		t.Error(err)
	}

	fmt.Println("==============json=====================")
	ss, err := json.Marshal(genesisblock)
	if err != nil {
		t.Error(err)
	}
	fmt.Println("genesisblock", string(ss))
}

func TestGenesisAccount_MarshalTOML(t *testing.T) {
	genesisblock := GenesisAccount{
		Nonce:      100,
		Code:       []byte("hhhhh"),
		PrivateKey: []byte("hhhh2222h"),
	}
	fmt.Println("===================================")
	err := toml.NewEncoder(os.Stdout).Encode(genesisblock)
	if err != nil {
		t.Error(err)
	}
}

func TestGenesisAccount_MarshalJson(t *testing.T) {
	genesisblock := GenesisAccount{
		Nonce:      100,
		Code:       []byte("hhhhh"),
		PrivateKey: []byte("hhhh2222h"),
	}
	fmt.Println("===================================")

	ss, err := json.Marshal(genesisblock)
	if err != nil {
		t.Error(err)
	}
	fmt.Println("ss", string(ss))
}

func TestTestnetGenesisBlock_MarshalTOML(t *testing.T) {
	origMode := configs.GetRunMode()
	configs.SetRunMode(configs.Testnet)
	genesisblock := DefaultGenesisBlock()
	fmt.Println("==============toml=====================")
	err := toml.NewEncoder(os.Stdout).Encode(genesisblock)
	if err != nil {
		t.Error(err)
	}

	fmt.Println("==============json=====================")
	ss, err := json.Marshal(genesisblock)
	if err != nil {
		t.Error(err)
	}
	fmt.Println("genesisblock", string(ss))
	configs.SetRunMode(origMode)
}

func TestMainnetGenesisBlock_MarshalTOML(t *testing.T) {
	origMode := configs.GetRunMode()
	configs.SetRunMode(configs.Mainnet)
	genesisblock := DefaultGenesisBlock()
	fmt.Println("==============toml=====================")
	err := toml.NewEncoder(os.Stdout).Encode(genesisblock)
	if err != nil {
		t.Error(err)
	}

	fmt.Println("==============json=====================")
	ss, err := json.Marshal(genesisblock)
	if err != nil {
		t.Error(err)
	}
	fmt.Println("genesisblock", string(ss))
	configs.SetRunMode(origMode)
}
