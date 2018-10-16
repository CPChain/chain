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
	"github.com/cespare/cp"
	"path/filepath"
	"runtime"
	"testing"
)

// These tests are 'smoke tests' for the account related
// subcommands and flags.
//
// For most tests, the test files from package accounts
// are copied into a temporary keystore directory.
func tmpDatadirWithKeystore(t *testing.T) string {
	datadir := tmpdir(t)
	keystore := filepath.Join(datadir, "keystore")
	source := filepath.Join("..", "..", "accounts", "keystore", "testdata", "keystore")
	if err := cp.CopyAll(keystore, source); err != nil {
		t.Fatal(err)
	}
	return datadir
}

func TestAccountListEmpty(t *testing.T) {
	datadir := tmpdir(t) + "/notexist/"
	geth := runGeth(t, "account", "list", "--datadir", datadir)
	geth.ExpectExit()
}

func TestAccountList(t *testing.T) {
	datadir := tmpDatadirWithKeystore(t)
	geth := runGeth(t, "account", "list", "--datadir", datadir)
	defer geth.ExpectExit()
	if runtime.GOOS == "windows" {
		geth.Expect(`
Account #0: {7ef5a6135f1fd6a02593eedc869c6d41d934aef8} keystore://{{.Datadir}}\keystore\UTC--2016-03-22T12-57-55.920751759Z--7ef5a6135f1fd6a02593eedc869c6d41d934aef8
Account #1: {f466859ead1932d743d622cb74fc058882e8648a} keystore://{{.Datadir}}\keystore\aaa
Account #2: {289d485d9771714cce91d3393d764e1311907acc} keystore://{{.Datadir}}\keystore\zzz
`)
	} else {
		geth.Expect(`
Account #0: {7ef5a6135f1fd6a02593eedc869c6d41d934aef8} keystore://{{.Datadir}}/keystore/UTC--2016-03-22T12-57-55.920751759Z--7ef5a6135f1fd6a02593eedc869c6d41d934aef8
Account #1: {f466859ead1932d743d622cb74fc058882e8648a} keystore://{{.Datadir}}/keystore/aaa
Account #2: {289d485d9771714cce91d3393d764e1311907acc} keystore://{{.Datadir}}/keystore/zzz
`)
	}
}

func TestAccountNew(t *testing.T) {
	datadir := tmpDatadirWithKeystore(t)
	geth := runGeth(t, "account", "new", "--lightkdf", "--datadir", datadir)
	defer geth.ExpectExit()
	geth.Expect(`
Please input your password:{{.InputLine "foobar"}}
Please repeat:{{.InputLine "foobar"}}
`)
	geth.ExpectRegexp(`Address: \{[0-9a-f]{40}\}\n`)
}

func TestAccountNewBadRepeat(t *testing.T) {
	datadir := tmpDatadirWithKeystore(t)
	geth := runGeth(t, "account", "new", "--lightkdf", "--datadir", datadir)
	defer geth.ExpectExit()
	geth.Expect(`
Please input your password:{{.InputLine "something"}}
Please repeat:{{.InputLine "something_else"}}
Password doesn't match
Failed to readPassword
`)
}

func TestAccountUpdate(t *testing.T) {
	datadir := tmpDatadirWithKeystore(t)
	geth := runGeth(t, "account", "update",
		"--datadir", datadir, "--lightkdf",
		"f466859ead1932d743d622cb74fc058882e8648a")
	defer geth.ExpectExit()
	geth.Expect(`

Unlocking account f466859ead1932d743d622cb74fc058882e8648a | Attempt 1/3
Password:{{.InputLine "foobar"}}Please give a new password:{{.InputLine "foobar"}}Please repeat:{{.InputLine "foobar"}}
`)
}
func TestUnlockFlagWrongPassword(t *testing.T) {
	datadir := tmpDatadirWithKeystore(t)
	geth := runGeth(t, "run",
		"--datadir", datadir,
		"--unlock", "f466859ead1932d743d622cb74fc058882e8648a")
	// geth := runGeth(t, "run",
	// 	"--datadir", datadir, "--nat", "none", "--nodiscover", "--maxpeers", "0", "--port", "0",
	// 	"--unlock", "f466859ead1932d743d622cb74fc058882e8648a")
	defer geth.ExpectExit()
	geth.Expect(`
Unlocking account f466859ead1932d743d622cb74fc058882e8648a | Attempt 1/3
!! Unsupported terminal, password will be echoed.
Passphrase: {{.InputLine "wrong1"}}
Unlocking account f466859ead1932d743d622cb74fc058882e8648a | Attempt 2/3
Passphrase: {{.InputLine "wrong2"}}
Unlocking account f466859ead1932d743d622cb74fc058882e8648a | Attempt 3/3
Passphrase: {{.InputLine "wrong3"}}
Fatal: Failed to unlock account f466859ead1932d743d622cb74fc058882e8648a (could not decrypt key with given passphrase)
`)
}

func TestUnlockFlagWrongPassword11(t *testing.T) {
	datadir := tmpDatadirWithKeystore(t)
	geth := runGeth(t,
		"--datadir", datadir, "--nat", "none", "--nodiscover", "--maxpeers", "0", "--port", "0",
		"--unlock", "f466859ead1932d743d622cb74fc058882e8648a")
	defer geth.ExpectExit()
	geth.Expect(`
		   0.0.1
		
		AUTHOR:
		   The cpchain authors <info@cpchain.io>
		
		COMMANDS:
		     account     Manage accounts
		     chain       Manage blockchain
		     dumpconfig  Show configuration values
		     run         Run a cpchain node
		     help, h     Shows a list of commands or help for one command
		
		GLOBAL OPTIONS:
		   --config value  Path to TOML configuration file (default "<datadir>/config.toml")
		   --help, -h      Show help
		   --version, -v   Print the version
		
		COPYRIGHT:
		   LGPL
`)
}

func TestUnlockFlagPasswordFileWrongPassword(t *testing.T) {
	datadir := tmpDatadirWithKeystore(t)
	geth := runGeth(t,
		"--datadir", datadir, "--nat", "none", "--nodiscover", "--maxpeers", "0", "--port", "0",
		"--password", "testdata/wrong-passwords.txt", "--unlock", "0,2")
	defer geth.ExpectExit()
	geth.Expect(`
Fatal: Failed to unlock account 0 (could not decrypt key with given passphrase)
`)
}

func TestUnlockFlagAmbiguousWrongPassword(t *testing.T) {
	store := filepath.Join("..", "..", "accounts", "keystore", "testdata", "dupes")
	geth := runGeth(t,
		"--keystore", store, "--nat", "none", "--nodiscover", "--maxpeers", "0", "--port", "0",
		"--unlock", "f466859ead1932d743d622cb74fc058882e8648a")
	defer geth.ExpectExit()

	// Helper for the expect template, returns absolute keystore path.
	geth.SetTemplateFunc("keypath", func(file string) string {
		abs, _ := filepath.Abs(filepath.Join(store, file))
		return abs
	})
	geth.Expect(`
Unlocking account f466859ead1932d743d622cb74fc058882e8648a | Attempt 1/3
!! Unsupported terminal, password will be echoed.
Passphrase: {{.InputLine "wrong"}}
Multiple key files exist for address f466859ead1932d743d622cb74fc058882e8648a:
   keystore://{{keypath "1"}}
   keystore://{{keypath "2"}}
Testing your passphrase against all of them...
Fatal: None of the listed files could be unlocked.
`)
	geth.ExpectExit()
}
