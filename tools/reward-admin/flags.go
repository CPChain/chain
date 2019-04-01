package main

import (
	"context"
	"errors"

	"bitbucket.org/cpchain/chain/tools/reward-admin/common"
	"bitbucket.org/cpchain/chain/tools/reward-admin/manager"
	"bitbucket.org/cpchain/chain/tools/reward-admin/output"
	"bitbucket.org/cpchain/chain/tools/utility"
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

func build(ctx *cli.Context) (*manager.Console, common.Output, context.CancelFunc) {
	rpc, kspath, pwdfile, err := validator(ctx)
	out := output.NewLogOutput()
	if err != nil {
		out.Fatal(err.Error())
	}
	_ctx, cancel := context.WithCancel(context.Background())
	console := manager.NewConsole(&_ctx, rpc, kspath, pwdfile, &out)
	return console, &out, cancel
}

var home, err = utility.Home()

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

	if !utility.Exists(pwdfile) {
		err = errors.New("Password file " + pwdfile + " does not exist.")
		return rpc, kspath, pwdfile, err
	}
	if !utility.Exists(kspath) {
		err = errors.New("Keystore file " + kspath + " does not exist.")
		return rpc, kspath, pwdfile, err
	}
	return rpc, kspath, pwdfile, nil
}
