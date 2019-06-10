package flags

import (
	"errors"

	"bitbucket.org/cpchain/chain/tools/utility"
	"github.com/urfave/cli"
)

var home, err = utility.Home()

func init() {
	if err != nil {
		panic(err)
	}
}

// RPCFlags set the APIs offered over the HTTP-RPC interface
var RPCFlags = []cli.Flag{

	cli.StringFlag{
		Name:  "rpc",
		Usage: "Set the APIs offered over the HTTP-RPC interface",
		Value: "http://127.0.0.1:8501",
	},
}

// campaignAccountFlags include account params
var campaignAccountFlags = []cli.Flag{
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

var GasFlags = []cli.Flag{
	cli.Int64Flag{
		Name:  "gasprice",
		Usage: "Gas Price, unit is Wei, default is suggested gas price from server",
	},
	cli.Int64Flag{
		Name:  "gaslimit",
		Usage: "Gas Limit, default 2000000",
		Value: 2000000,
	},
}

func WrapperFlags(flags []cli.Flag) []cli.Flag {
	flags = append(flags, RPCFlags...)
	flags = append(flags, campaignAccountFlags...)
	return flags
}

func Validator(ctx *cli.Context) (string, string, string, error) {
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
