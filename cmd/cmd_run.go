package main

import (
	"bitbucket.org/cpchain/chain/eth"
	"os"
	"os/signal"
	"strings"
	"syscall"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/ethclient"
	"bitbucket.org/cpchain/chain/node"
	"github.com/ethereum/go-ethereum/log"
	"github.com/urfave/cli"
)

var runCommand cli.Command

func init() {
	flags := append(nodeFlags, rpcFlags...)
	// flags = append(flags, consoleFlags...)
	runCommand = cli.Command{
		Action:      run,
		Name:        "run",
		Flags:       flags,
		Category:    "Run",
		Description: "Run a cpchain node",
	}
}

func run(ctx *cli.Context) error {
	n := createNode(ctx)
	bootstrap(ctx, n)
	n.Wait()
	return nil
}


func handleNode(ctx *cli.Context, n *node.Node) {
	// launch the node itself
	if err := n.Start(); err != nil {
		Fatalf("Error starting protocol n: %v", err)
	}
}


func handleAccount(ctx *cli.Context, n *node.Node) {
	// Unlock any account specifically requested
	ks := n.AccountManager().Backends(keystore.KeyStoreType)[0].(*keystore.KeyStore)

	passwords := MakePasswordList(ctx)
	unlocks := strings.Split(ctx.GlobalString(UnlockedAccountFlag.Name), ",")
	for i, account := range unlocks {
		if trimmed := strings.TrimSpace(account); trimmed != "" {
			unlockAccount(ctx, ks, trimmed, i, passwords)
		}
	}
	// Register wallet event handlers to open and auto-derive wallets
	events := make(chan accounts.WalletEvent, 16)
	n.AccountManager().Subscribe(events)

	var contractCaller *dpor.ContractCaller
	// TODO: @liuq fix this.
	if len(ks.Accounts()) > 0 && len(passwords) > 0 {
		account := ks.Accounts()[0]
		account, key, err := ks.GetDecryptedKey(account, passwords[0])
		if err != nil {
			log.Warn("err when get account", "err", err)
		}
		log.Warn("succeed when get unlock account", "key", key)

		rpcClient, err := n.Attach()
		if err != nil {
			Fatalf("Failed to attach to self: %v", err)
		}
		client := ethclient.NewClient(rpcClient)

		contractCaller, err = dpor.NewContractCaller(key, client, 300000, 1)
		if err != nil {
			log.Warn("err when make contract call", "err", err)
		}
	}

	if ctx.GlobalBool(MiningEnabledFlag.Name) {
		var ethereum *eth.Ethereum
		if err := n.Service(&ethereum); err != nil {
			Fatalf("Ethereum service not running: %v", err)
		}

		if err := ethereum.StartMining(true, contractCaller); err != nil {
			Fatalf("Failed to start mining: %v", err)
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
	handleNode(ctx, n)

	handleAccount(ctx, n)

	// handleMiner(ctx, n)

	// handle user interrupt
	go handleInterrupt(n)
}


// func handleMiner(ctx *cli.Context, n *node.Node) {
// }
