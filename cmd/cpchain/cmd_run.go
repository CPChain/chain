package main

import (
	"os"
	"os/signal"
	"syscall"

	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/eth"
	"bitbucket.org/cpchain/chain/node"
	"github.com/urfave/cli"
)

var runCommand cli.Command

func init() {
	runFlags := append([]cli.Flag(nil), flags.RpcFlags...)
	runFlags = append(runFlags, flags.GeneralFlags...)
	runFlags = append(runFlags, flags.NodeFlags...)
	runFlags = append(runFlags, flags.MinerFlags...)
	// flags = append(flags, consoleFlags...)
	runCommand = cli.Command{
		Action: run,
		Name:   "run",
		Flags:  runFlags,
		Usage:  "Run a cpchain node",
	}
}

func run(ctx *cli.Context) error {
	n := createNode(ctx)
	bootstrap(ctx, n)
	n.Wait()
	return nil
}

// Creates a node with chain services registered
func createNode(ctx *cli.Context) *node.Node {
	cfg, n := newConfigNode(ctx)
	registerChainService(&cfg.Eth, n)
	return n
}

// Starts up the node
func startNode(n *node.Node) {
	// launch the node itself
	if err := n.Start(); err != nil {
		log.Fatalf("Error starting protocol n: %v", err)
	}
}

func unlockAccounts(ctx *cli.Context, n *node.Node) {
	// ks := n.AccountManager().Backends(keystore.KeyStoreType)[0].(*keystore.KeyStore)
	//
	// passwords := utils.MakePasswordList(ctx)
	// unlocks := strings.Split(ctx.GlobalString(utils.UnlockedAccountFlag.Name), ",")
	// for i, account := range unlocks {
	// 	if trimmed := strings.TrimSpace(account); trimmed != "" {
	// 		unlockAccount(ctx, ks, trimmed, i, passwords)
	// 	}
	// }
}

func handleWallet() {
	// i am not sure what exactly it does, and if the functionality here is useful for us.
}

func startMining(ctx *cli.Context, n *node.Node) {
	if ctx.Bool("mine") {
		var ethereum *eth.Ethereum
		if err := n.Service(&ethereum); err != nil {
			log.Fatalf("Ethereum service not running: %v", err)
		}
		// Use a reduced number of threads if requested
		if threads := ctx.Int("minethreads"); threads > 0 {
			type threaded interface {
				SetThreads(threads int)
			}
			if th, ok := ethereum.Engine().(threaded); ok {
				th.SetThreads(threads)
			}
		}
		// // Set the gas price to the limits from the CLI and start mining
		// ethereum.TxPool().SetGasPrice(utils.GlobalBig(ctx, utils.GasPriceFlag.Name))


		// TODO dpor contract caller
		if err := ethereum.StartMining(true, nil); err != nil {
			log.Fatalf("Failed to start mining: %v", err)
		}
	}
}

func handleInterrupt(n *node.Node) {
	sigc := make(chan os.Signal, 1)
	signal.Notify(sigc, syscall.SIGINT, syscall.SIGTERM)
	defer signal.Stop(sigc)
	<-sigc
	log.Info("Got interrupt, shutting down...")
	go n.Stop()
	for i := 10; i > 0; i-- {
		<-sigc
		if i > 1 {
			log.Warn("Already shutting down, interrupt more to panic.", "times", i-1)
		}
	}
}

func bootstrap(ctx *cli.Context, n *node.Node) {
	startNode(n)
	unlockAccounts(ctx, n)
	handleWallet()
	startMining(ctx, n)
	// handle user interrupt
	go handleInterrupt(n)
}
