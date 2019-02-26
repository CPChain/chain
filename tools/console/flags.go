package main

import (
	"errors"

	"bitbucket.org/cpchain/chain/tools/console/common"
	"github.com/urfave/cli"
)

// RPCFlags set the APIs offered over the HTTP-RPC interface
var RPCFlags = []cli.Flag{

	cli.StringFlag{
		Name:  "rpc",
		Usage: "Set the APIs offered over the HTTP-RPC interface",
		Value: "http://127.0.0.1:8501",
	},
}

var home, err = common.Home()

func init() {
	if err != nil {
		panic(err)
	}
}

// AccountFlags include account params
var AccountFlags = []cli.Flag{
	// do not marshal the keystore path in toml file.
	cli.StringFlag{
		Name:  "password",
		Usage: "Password file to use for non-interactive password input",
		Value: home + "/.cpchain/password",
	},
	cli.StringFlag{
		Name:  "keystore",
		Usage: "Keystore directory",
		Value: home + "/.cpchain/keystore/",
	},
}

func wrapperFlags(flags []cli.Flag) []cli.Flag {
	flags = append(flags, RPCFlags...)
	flags = append(flags, AccountFlags...)
	return flags
}

func validator(ctx *cli.Context) (string, string, string, error) {
	pwdfile := ctx.String("password")
	kspath := ctx.String("keystore")
	rpc := ctx.String("rpc")

	if !common.Exists(pwdfile) {
		err = errors.New(pwdfile + " is not exists.")
		return rpc, kspath, pwdfile, err
	}
	if !common.Exists(kspath) {
		err = errors.New(kspath + " is not exists.")
		return rpc, kspath, pwdfile, err
	}
	return rpc, kspath, pwdfile, nil
}
