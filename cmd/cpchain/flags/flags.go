package flags

import (
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/node"
	"fmt"
	"github.com/urfave/cli"
	"path/filepath"
)

var flagMap = make(map[string]cli.Flag)

func init() {
	cli.VersionFlag = cli.BoolFlag{
		Name:  "version, v",
		Usage: "Print the version",
	}

	cli.HelpFlag = cli.BoolFlag{
		Name:  "help, h",
		Usage: "Show help",
	}

	Register(ConfigFileFlag)
	Register(GeneralFlags...)
	Register(AccountFlags...)
	Register(RpcFlags...)
	Register(MiscFlags...)
}

func Register(flags ...cli.Flag) {
	for _, flag := range flags {
		if _, ok := flagMap[flag.GetName()]; ok {
			log.Fatalf("Flag already exists: %v", flag.GetName())
		}
		flagMap[flag.GetName()] = flag
	}
}

func GetByName(name string) cli.Flag {
	flag, ok := flagMap[name]
	if !ok {
		log.Fatalf("Flag does not exist: %v", name)
	}
	return flag
}

// begin flags
// **********************************************************************************************************

// this should be a global option
var ConfigFileFlag = cli.StringFlag{
	Name: "config",
	Usage: fmt.Sprintf("Path to TOML configuration file (default %q)",
		filepath.Join(node.DefaultDataDir(), "config.toml")),
}


var GeneralFlags = []cli.Flag{
	cli.StringFlag{
		Name:  "datadir",
		Usage: "Data directory for the databases and keystore",
		Value: node.DefaultDataDir(),
	},
}

// TODO @xumx  adjust the following
var AccountFlags = []cli.Flag{
	// i feel that the keystore path only causes confusion.
	// let it reside in $datadir is fair enough.
	// TODO do not marshal the keystore path in toml file.
	// cli.StringFlag{
	// 	Name:  "keystore",
	// 	Usage: "Directory for the keystore (default = inside the datadir)",
	// },

	cli.StringFlag{
		Name:  "unlock",
		Usage: "Comma separated list of accounts to unlock",
		Value: "",
	},
}

var ChainFlags = []cli.Flag{
	cli.Uint64Flag{
		Name:  "networkid",
		Usage: "Network identifier (integer, mainnet=0, testnet=1)",
	},
	cli.StringFlag{
		Name:  "password",
		Usage: "Password file to use for non-interactive password input",
		Value: "",
	},
	cli.StringFlag{
		Name:  "account",
		Usage: "Public address for block mining rewards. Use the first account if none is provided.",
	},
}

var MinerFlags = []cli.Flag{
	cli.BoolFlag{
		Name:  "mine",
		Usage: "Enable mining",
	},
	cli.IntFlag{
		Name:  "minethreads",
		Usage: "Thread count for mining",
		Value: 4,
	},
}

// TODO @sangh adjust these
var RpcFlags = []cli.Flag{
	cli.BoolFlag{
		Name:  "rpc",
		Usage: "Enable the HTTP-RPC server",
	},

	cli.StringFlag{
		Name:  "rpcaddr",
		Usage: "HTTP-RPC server listening interface",
	},
	cli.IntFlag{
		Name:  "rpcport",
		Usage: "HTTP-RPC server listening port",
	},
}

// TODO @liuq  adjust the following
// p2p flags
var P2pFlags = []cli.Flag{
	cli.IntFlag{
		Name:  "maxpeers",
		Usage: "Maximum number of network peers (network disabled if set to 0)",
	},
	cli.IntFlag{
		Name:  "maxpendpeers",
		Usage: "Maximum number of pending connection attempts (defaults used if set to 0)",
	},
	cli.IntFlag{
		Name:  "port",
		Usage: "Network listening port",
		Value: 30303,
	},
	cli.StringFlag{
		Name:  "bootnodes",
		Usage: "Comma separated enode URLs for P2P discovery bootstrap (set v4+v5 instead for light servers)",
		Value: "",
	},
	cli.StringFlag{
		Name:  "nodekey",
		Usage: "P2P node key file",
	},
}

var NodeFlags = []cli.Flag{
	cli.StringFlag{
		Name:  "identity",
		Usage: "Custom node name",
	},
}

var MiscFlags = []cli.Flag{}
