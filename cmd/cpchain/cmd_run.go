package main

import (
	"os"
	"os/signal"
	"strings"
	"syscall"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/eth"
	"bitbucket.org/cpchain/chain/ethclient"
	"bitbucket.org/cpchain/chain/node"
	"github.com/urfave/cli"
)

var runCommand cli.Command

func init() {
	runFlags := append([]cli.Flag(nil), flags.RpcFlags...)
	runFlags = append(runFlags, flags.GeneralFlags...)
	runFlags = append(runFlags, flags.NodeFlags...)
	runFlags = append(runFlags, flags.MinerFlags...)
	runFlags = append(runFlags, flags.P2pFlags...)
	runFlags = append(runFlags, flags.AccountFlags...)
	runFlags = append(runFlags, flags.ChainFlags...)
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
	ks := n.AccountManager().Backends(keystore.KeyStoreType)[0].(*keystore.KeyStore)
	unlocks := strings.Split(ctx.String(flags.UnlockFlagName), ",")
	for _, account := range unlocks {
		if trimmed := strings.TrimSpace(account); trimmed != "" {
			unlockAccount(ctx, ks, trimmed)
		}
	}
}

func handleWallet(n *node.Node) {
	// Register wallet event handlers to open and auto-derive wallets
	events := make(chan accounts.WalletEvent, 16)
	n.AccountManager().Subscribe(events)

	go func() {
		// Create a chain state reader for self-derivation
		rpcClient, err := n.Attach()
		if err != nil {
			log.Fatalf("Failed to attach to self: %v", err)
		}
		stateReader := ethclient.NewClient(rpcClient)

		// Open any wallets already attached
		for _, wallet := range n.AccountManager().Wallets() {
			if err := wallet.Open(""); err != nil {
				log.Warn("Failed to open wallet", "url", wallet.URL(), "err", err)
			}
		}
		// Listen for wallet event till termination
		for event := range events {
			switch event.Kind {
			case accounts.WalletArrived:
				if err := event.Wallet.Open(""); err != nil {
					log.Warn("New wallet appeared, failed to open", "url", event.Wallet.URL(), "err", err)
				}
			case accounts.WalletOpened:
				status, _ := event.Wallet.Status()
				log.Info("New wallet appeared", "url", event.Wallet.URL(), "status", status)

				if event.Wallet.URL().Scheme == "ledger" {
					event.Wallet.SelfDerive(accounts.DefaultLedgerBaseDerivationPath, stateReader)
				} else {
					event.Wallet.SelfDerive(accounts.DefaultBaseDerivationPath, stateReader)
				}

			case accounts.WalletDropped:
				log.Info("Old wallet dropped", "url", event.Wallet.URL())
				event.Wallet.Close()
			}
		}
	}()
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

		contractCaller := createContractCaller(ctx, n)
		if err := ethereum.StartMining(true, contractCaller); err != nil {
			log.Fatalf("Failed to start mining: %v", err)
		}
	}
}

func createContractCaller(ctx *cli.Context, n *node.Node) *dpor.ContractCaller {
	ks := n.AccountManager().Backends(keystore.KeyStoreType)[0].(*keystore.KeyStore)
	passwords := makePasswordList(ctx)
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
			log.Fatalf("Failed to attach to self: %v", err)
		}
		client := ethclient.NewClient(rpcClient)

		contractCaller, err = dpor.NewContractCaller(key, client, 300000, 1)
		if err != nil {
			log.Warn("err when make contract call", "err", err)
		}
	}
	return contractCaller
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
	handleWallet(n)
	startMining(ctx, n)
	// handle user interrupt
	go handleInterrupt(n)
}
