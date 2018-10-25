package flags

import (
	"fmt"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/node"
	"github.com/urfave/cli"
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
	Register(ChainFlags...)
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
	Name:  "config",
	Usage: fmt.Sprintf("Path to TOML configuration file (default \"<datadir>/config.toml\")"),
}

const (
	DataDirFlagName = "datadir"
)

var GeneralFlags = []cli.Flag{
	cli.StringFlag{
		Name:  DataDirFlagName,
		Usage: "Data directory for the database and keystore",
		Value: node.DefaultDataDir(),
	},
}

const (
	PasswordFlagName = "password"
	LightKdfFlagName = "lightkdf"
	UnlockFlagName   = "unlock"
)

var AccountFlags = []cli.Flag{
	// do not marshal the keystore path in toml file.
	cli.StringFlag{
		Name:  PasswordFlagName,
		Usage: "Password file to use for non-interactive password input",
		Value: "",
	},
	cli.BoolFlag{
		Name:  LightKdfFlagName,
		Usage: "Reduce key-derivation RAM & CPU usage at some expense of KDF strength",
	},
	cli.StringFlag{
		Name:  UnlockFlagName,
		Usage: "Comma separated list of accounts to unlock",
		Value: "",
	},
}

const (
	NetworkIDFlagName     = "networkid"
	NoCompactionFlagName  = "nocompaction"
	CacheFlagName         = "cache"
	CacheDatabaseFlagName = "cache.database"
	CacheGCFlagName       = "cache.gc"
)

var ChainFlags = []cli.Flag{
	cli.Uint64Flag{
		Name:  NetworkIDFlagName,
		Usage: "Network identifier (integer, mainnet=0, testnet=1)",
	},
	cli.StringFlag{
		Name:  "account",
		Usage: "Public address for block mining rewards. Use the first account if none is provided.",
	},
	cli.BoolFlag{
		Name:  NoCompactionFlagName,
		Usage: "Disables db compaction after import",
	},
	cli.IntFlag{
		Name:  CacheFlagName,
		Usage: "Megabytes of memory allocated to internal caching",
		Value: 1024,
	},
	cli.IntFlag{
		Name:  CacheDatabaseFlagName,
		Usage: "Percentage of cache memory allowance to use for database io",
		Value: 75,
	},
	cli.IntFlag{
		Name:  CacheGCFlagName,
		Usage: "Percentage of cache memory allowance to use for trie pruning",
		Value: 25,
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

// const (
// 	RpcFlagName       = "rpc"
// 	RpcAddrFlagName   = "rpcaddr"
// 	RpcPortFlagName   = "rpcport"
// 	RpcTlsFlagName    = "rpctls"
// 	RpcVerifyFlagName = "rpcverify"
// )

const (
	IpcAddrFlagName = "ipcaddr"
	RpcAddrFlagName = "rpcaddr"
	// these two flags should be removed in the future
	GRpcAddrFlagName     = "grpcaddr"
	GatewayAddrFlagName  = "gatewayaddr"
	RpcCorDomainFlagName = "rpccorsdomain"
)

// TODO @sangh adjust these
var RpcFlags = []cli.Flag{
	// cli.BoolFlag{
	// 	Name:  RpcFlagName,
	// 	Usage: "Enable the HTTP-RPC server",
	// },
	//
	// cli.StringFlag{
	// 	Name:  RpcAddrFlagName,
	// 	Usage: "HTTP-RPC server listening interface",
	// },
	// cli.IntFlag{
	// 	Name:  RpcPortFlagName,
	// 	Usage: "HTTP-RPC server listening port",
	// },
	// cli.BoolFlag{
	// 	Name:  RpcTlsFlagName,
	// 	Usage: "HTTP-RPC server is need tls transport",
	// },
	// cli.BoolFlag{
	// 	Name:  RpcVerifyFlagName,
	// 	Usage: "HTTP-RPC server if need verify client",
	// },
	cli.StringFlag{
		Name:  IpcAddrFlagName,
		Usage: "Local ipc path",
	},
	cli.StringFlag{
		Name:  RpcAddrFlagName,
		Usage: "RPC address whose format is <host:port>",
	},
	cli.StringFlag{
		Name:  GRpcAddrFlagName,
		Usage: "GRPC address whose format is <host:port>",
	},
	cli.StringFlag{
		Name:  GatewayAddrFlagName,
		Usage: "GRPC gateway address whose format is <host:port>",
	},
	cli.StringFlag{
		Name:  RpcCorDomainFlagName,
		Usage: "Comma separated list of domains from which to accept cross origin requests (browser enforced)",
	},
}

const (
	MaxPeersFlagName        = "maxpeers"
	MaxPendingPeersFlagName = "maxpendpeers"
	PortFlagName            = "port"
	BootnodesFlagName       = "bootnodes"
	NodeKeyFileFlagName     = "nodekey"
)

// TODO @chengxin  adjust the following  {ac}
// p2p flags
var P2pFlags = []cli.Flag{
	cli.IntFlag{
		Name:  MaxPeersFlagName,
		Usage: "Maximum number of network peers (network disabled if set to 0)",
	},
	cli.IntFlag{
		Name:  MaxPendingPeersFlagName,
		Usage: "Maximum number of pending connection attempts (defaults used if set to 0)",
	},
	cli.IntFlag{
		Name:  PortFlagName,
		Usage: "Network listening port",
		Value: 30303,
	},
	cli.StringFlag{
		Name:  BootnodesFlagName,
		Usage: "Comma separated enode URLs for P2P discovery bootstrap (set v4+v5 instead for light servers)",
		Value: "",
	},
	cli.StringFlag{
		Name:  NodeKeyFileFlagName,
		Usage: "P2P node key file",
	},
}

const (
	IdentityFlagName = "identity"
	ProfileFlagName  = "profile"
)

var NodeFlags = []cli.Flag{
	cli.StringFlag{
		Name:  IdentityFlagName,
		Usage: "Customized node name",
	},
	cli.StringFlag{
		Name:  ProfileFlagName,
		Usage: "Profile the running cpchain instance, output to the specified dir path",
	},
}

var MiscFlags = []cli.Flag{}
