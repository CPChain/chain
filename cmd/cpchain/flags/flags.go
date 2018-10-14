package flags

import (
	"bitbucket.org/cpchain/chain/node"
	"fmt"
	"io"
	"os"
	"runtime"

	"github.com/urfave/cli"
)

var flagMap = make(map[string]cli.Flag)

// Fatalf formats a message to standard error and exits the program.
// The message is also printed to standard output if standard error
// is redirected to a different file.
func Fatalf(format string, args ...interface{}) {
	w := io.MultiWriter(os.Stdout, os.Stderr)
	if runtime.GOOS == "windows" {
		// The SameFile check below doesn't work on Windows.
		// stdout is unlikely to get redirected though, so just print there.
		w = os.Stdout
	} else {
		outf, _ := os.Stdout.Stat()
		errf, _ := os.Stderr.Stat()
		if outf != nil && errf != nil && os.SameFile(outf, errf) {
			w = os.Stderr
		}
	}
	fmt.Fprintf(w, "Fatal: "+format+"\n", args...)
	os.Exit(1)
}

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
			Fatalf("Flag already exists: %v", flag.GetName())
		}
		flagMap[flag.GetName()] = flag
	}
}

func GetByName(name string) cli.Flag {
	flag, ok := flagMap[name]
	if !ok {
		Fatalf("Flag does not exist: %v", name)
	}
	return flag
}


// begin flags
// **********************************************************************************************************

// this should be a global option
var ConfigFileFlag = cli.StringFlag{
	Name:  "config",
	Usage: "Location of the TOML format configuration file",
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
	cli.StringFlag{
		Name:  "keystore",
		Usage: "Directory for the keystore (default = inside the datadir)",
	},

	cli.StringFlag{
		Name:  "unlock",
		Usage: "Comma separated list of accounts to unlock",
		Value: "",
	},
}

var ChainFlags = []cli.Flag{
	cli.Uint64Flag{
		Name:  "networkid",
		Usage: "Network identifier (integer, 1=Frontier, 2=Morden (disused), 3=Ropsten, 4=Rinkeby)",
	},
	cli.StringFlag{
		Name:  "password",
		Usage: "Password file to use for non-interactive password input",
		Value: "",
	},
}

var MinerFlags = []cli.Flag{
	cli.BoolFlag{
		Name:  "mine",
		Usage: "Enable mining",
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

var MiscFlags = []cli.Flag {
}
