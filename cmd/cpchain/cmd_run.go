// Copyright 2018 The cpchain authors
// This file is part of cpchain.
//
// cpchain is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// cpchain is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with cpchain. If not, see <http://www.gnu.org/licenses/>.

package main

import (
	"io/ioutil"
	"os"
	"os/signal"
	"strings"
	"syscall"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/commons/chainmetrics"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/primitive_register"
	"bitbucket.org/cpchain/chain/internal/profile"
	"bitbucket.org/cpchain/chain/node"
	"bitbucket.org/cpchain/chain/protocols/cpc"
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
	runFlags = append(runFlags, flags.LogFlags...)
	runCommand = cli.Command{
		Action: run,
		Name:   "run",
		Flags:  runFlags,
		Usage:  "Run a cpchain node",
		Before: func(ctx *cli.Context) error {
			return nil
		},
		After: func(ctx *cli.Context) error {
			if ctx.IsSet(flags.ProfileFlagName) {
				profile.Stop()
			}
			log.Info("Exit \"cpchain run\" command")
			return nil
		},
	}
}

func run(ctx *cli.Context) error {
	n := createNode(ctx)
	bootstrap(ctx, n)
	n.Wait()
	return nil
}

// Register chain services for a *full* node.
func registerChainService(cfg *cpc.Config, n *node.Node, cliCtx *cli.Context) {
	err := n.Register(func(ctx *node.ServiceContext) (node.Service, error) {
		fullNode, err := cpc.New(ctx, cfg)
		primitive_register.RegisterPrimitiveContracts()

		if cliCtx.Bool("mine") {
			fullNode.SetAsMiner(true)
		}
		return fullNode, err
	})
	if err != nil {
		log.Fatalf("Failed to register the chain service: %v", err)
	}
}

// Creates a node with chain services registered
func createNode(ctx *cli.Context) *node.Node {
	cfg, n := newConfigNode(ctx)
	registerChainService(&cfg.Cpc, n, ctx)
	return n
}

// Starts up the node
func startNode(n *node.Node) {
	// launch the node itself
	if err := n.Start(); err != nil {
		log.Fatalf("Error starting protocol n: %v", err)
	}
}

// makePasswordList reads password lines from the file specified by the global --password flag.
func makePasswordList(ctx *cli.Context) []string {
	path := ctx.String(flags.PasswordFlagName)
	if path == "" {
		return nil
	}
	text, err := ioutil.ReadFile(path)
	if err != nil {
		log.Fatalf("Failed to read password file: %v", err)
	}
	lines := strings.Split(string(text), "\n")
	// Sanitise DOS line endings.
	for i := range lines {
		lines[i] = strings.TrimRight(lines[i], "\r")
	}
	return lines
}

func unlockAccounts(ctx *cli.Context, n *node.Node) {
	ks := n.AccountManager().Backends(keystore.KeyStoreType)[0].(*keystore.KeyStore)
	passwords := makePasswordList(ctx)
	unlock := ctx.String("unlock")
	unlocks := strings.FieldsFunc(unlock, func(c rune) bool { return c == ',' })
	for i, account := range unlocks {
		log.Infof("%v, %v\n", i, account)
		if i < len(passwords) {
			unlockAccountWithPassword(ks, account, passwords[i])
		} else {
			unlockAccountWithPrompt(ks, account)
		}
	}
}

// TODO @chengxin @xumx please be sure about the underlying logic.
// cf. those in the keystore package.
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
		stateReader := cpclient.NewClient(rpcClient)

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
	var cpchainService *cpc.CpchainService
	// cpchainService will point to the real cpchain service in n.services
	if err := n.Service(&cpchainService); err != nil {
		log.Fatalf("Cpchain service not running: %v", err)
	}

	rpcClient, err := n.Attach()
	if err != nil {
		log.Fatalf("Failed to attach to self: %v", err)
	}
	client := cpclient.NewClient(rpcClient)
	cpchainService.SetClientForDpor(client)

	if ctx.Bool(flags.MineFlagName) {
		// TODO: fix this, do not use *keystore.Key, use wallet instead
		contractCaller := createContractCaller(ctx, n)
		if contractCaller != nil {
			cpchainService.AdmissionApiBackend.SetAdmissionKey(contractCaller.Key)
		}
		if err := cpchainService.StartMining(true, client); err != nil {
			log.Fatalf("Failed to start mining: %v", err)
		}
	}
}

// TODO to be removed.  do not add it here.
func createContractCaller(ctx *cli.Context, n *node.Node) *backend.ContractCaller {
	ks := n.AccountManager().Backends(keystore.KeyStoreType)[0].(*keystore.KeyStore)
	passwords := makePasswordList(ctx)
	var contractCaller *backend.ContractCaller
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
		client := cpclient.NewClient(rpcClient)

		// TODO: @Liuq fix this.
		contractCaller, err = backend.NewContractCaller(key, client, 300000)
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
	// start profiling
	if ctx.IsSet(flags.ProfileFlagName) {
		if err := profile.Start(ctx); err != nil {
			log.Fatalf("start profiling failed: %v\n", err)
		}
	}

	// init metrics
	if ctx.IsSet(flags.MetricGatewayFlagName) {
		chainmetrics.InitMetrics(ctx.String(flags.PortFlagName), ctx.String(flags.MetricGatewayFlagName))
	}

	startNode(n)
	unlockAccounts(ctx, n)
	handleWallet(n)
	startMining(ctx, n)
	// handle user interrupt
	go handleInterrupt(n)
}
