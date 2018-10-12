package main

import (
	"os"
	"os/signal"
	"strings"
	"syscall"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/eth"
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
	node := makeFullNode(ctx)
	startNode(ctx, node)
	node.Wait()
	return nil
}

func StartNode(stack *node.Node) {
	if err := stack.Start(); err != nil {
		Fatalf("Error starting protocol stack: %v", err)
	}
	go func() {
		sigc := make(chan os.Signal, 1)
		signal.Notify(sigc, syscall.SIGINT, syscall.SIGTERM)
		defer signal.Stop(sigc)
		<-sigc
		log.Info("Got interrupt, shutting down...")
		go stack.Stop()
		for i := 10; i > 0; i-- {
			<-sigc
			if i > 1 {
				log.Warn("Already shutting down, interrupt more to panic.", "times", i-1)
			}
		}
	}()
}

// startNode boots up the system node and all registered protocols, after which
// it unlocks any requested accounts, and starts the RPC/IPC interfaces and the
// miner.
func startNode(ctx *cli.Context, stack *node.Node) {

	// Start up the node itself
	StartNode(stack)

	// Unlock any account specifically requested
	ks := stack.AccountManager().Backends(keystore.KeyStoreType)[0].(*keystore.KeyStore)

	passwords := MakePasswordList(ctx)
	unlocks := strings.Split(ctx.GlobalString(UnlockedAccountFlag.Name), ",")
	for i, account := range unlocks {
		if trimmed := strings.TrimSpace(account); trimmed != "" {
			unlockAccount(ctx, ks, trimmed, i, passwords)
		}
	}
	// Register wallet event handlers to open and auto-derive wallets
	events := make(chan accounts.WalletEvent, 16)
	stack.AccountManager().Subscribe(events)

	var contractCaller *dpor.ContractCaller
	// TODO: @liuq fix this.
	if len(ks.Accounts()) > 0 && len(passwords) > 0 {
		account := ks.Accounts()[0]
		account, key, err := ks.GetDecryptedKey(account, passwords[0])
		if err != nil {
			log.Warn("err when get account", "err", err)
		}
		log.Warn("succeed when get unlock account", "key", key)

		rpcClient, err := stack.Attach()
		if err != nil {
			Fatalf("Failed to attach to self: %v", err)
		}
		client := ethclient.NewClient(rpcClient)

		contractCaller, err = dpor.NewContractCaller(key, client, 300000, 1)
		if err != nil {
			log.Warn("err when make contract call", "err", err)
		}
	}

	// TODO: @liuq fix above.

	go func() {
		// Create a chain state reader for self-derivation
		rpcClient, err := stack.Attach()
		if err != nil {
			Fatalf("Failed to attach to self: %v", err)
		}
		stateReader := ethclient.NewClient(rpcClient)

		// Open any wallets already attached
		for _, wallet := range stack.AccountManager().Wallets() {
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
	// Start auxiliary services if enabled
	if ctx.GlobalBool(MiningEnabledFlag.Name) {
		var ethereum *eth.Ethereum
		if err := stack.Service(&ethereum); err != nil {
			Fatalf("Ethereum service not running: %v", err)
		}
		// Use a reduced number of threads if requested
		if threads := ctx.GlobalInt(MinerThreadsFlag.Name); threads > 0 {
			type threaded interface {
				SetThreads(threads int)
			}
			if th, ok := ethereum.Engine().(threaded); ok {
				th.SetThreads(threads)
			}
		}
		// Set the gas price to the limits from the CLI and start mining
		ethereum.TxPool().SetGasPrice(GlobalBig(ctx, GasPriceFlag.Name))

		if err := ethereum.StartMining(true, contractCaller); err != nil {
			Fatalf("Failed to start mining: %v", err)
		}
	}
}
