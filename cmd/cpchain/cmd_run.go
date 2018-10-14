package main

import (
	"fmt"
	"os"
	"os/signal"
	"syscall"

	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/node"
	"github.com/urfave/cli"
)

var runCommand cli.Command

func init() {
	cmdFlags := append([]cli.Flag(nil), flags.RpcFlags...)
	cmdFlags = append(cmdFlags, flags.GeneralFlags...)
	// flags = append(flags, consoleFlags...)
	runCommand = cli.Command{
		Action: run,
		Name:   "run",
		Flags:  cmdFlags,
		Usage:  "Run a cpchain node",
	}
}

func run(ctx *cli.Context) error {
	fmt.Println(ctx.IsSet("datadir"))
	fmt.Println(ctx.String("datadir"))


	n := createNode(ctx)
	bootstrap(ctx, n)
	// n.Wait()
	return nil
}

func handleNode(ctx *cli.Context, n *node.Node) {
	// launch the node itself
	if err := n.Start(); err != nil {
		// TODO fatal
		// Fatalf("Error starting protocol n: %v", err)
	}
}

func handleAccount(ctx *cli.Context, n *node.Node) {
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
	handleNode(ctx, n)

	handleAccount(ctx, n)

	// handleMiner(ctx, n)

	// handle user interrupt
	go handleInterrupt(n)
}
