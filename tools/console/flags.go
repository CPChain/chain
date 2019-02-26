package main

import (
	"github.com/urfave/cli"
)

// RPCFlags set the APIs offered over the HTTP-RPC interface
var RPCFlags = []cli.Flag{

	cli.StringFlag{
		Name:  "rpc",
		Usage: "Set the APIs offered over the HTTP-RPC interface",
		Value: "",
	},
}

// AccountFlags include account params
var AccountFlags = []cli.Flag{
	// do not marshal the keystore path in toml file.
	cli.StringFlag{
		Name:  "password",
		Usage: "Password file to use for non-interactive password input",
		Value: "",
	},
	cli.StringFlag{
		Name:  "keystore",
		Usage: "Keystore directory",
		Value: "~/.cpchain/keystore",
	},
}
