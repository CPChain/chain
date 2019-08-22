package flags

import (
	"errors"

	"bitbucket.org/cpchain/chain/configs"
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
	},
	cli.StringFlag{
		Name:  "keystore",
		Usage: "Keystore file",
	},
}

var RunModeFlags = []cli.Flag{
	cli.StringFlag{
		Name:  RunModeFlagName,
		Usage: "Run mode for switch node configuration, eg:dev|testnet|mainnet|testmainnet",
		Value: configs.Mainnet.String(),
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
	flags = append(flags, RunModeFlags...)
	return flags
}

func Validator(ctx *cli.Context) (string, string, string, error) {
	kspath := ctx.String("keystore")
	rpc := ctx.String("rpc")
	pwdfile := ""
	if ctx.IsSet("password") {
		pwdfile = ctx.String("password")
		if !utility.Exists(pwdfile) {
			err = errors.New("Password file " + pwdfile + " does not exist.")
			return rpc, kspath, pwdfile, err
		}
	}

	if !utility.Exists(kspath) {
		err = errors.New("Keystore file " + kspath + " does not exist.")
		return rpc, kspath, pwdfile, err
	}
	return rpc, kspath, pwdfile, nil
}
