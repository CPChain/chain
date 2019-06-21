package network

import (
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/network"
	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"bitbucket.org/cpchain/chain/tools/contract-admin/utils"
	"github.com/urfave/cli"
)

var (
	NetworkCommand = cli.Command{
		Name:  "network",
		Usage: "Manage Network Contract",
		Description: `
		Manage Network Contract
		`,
		Flags: flags.GeneralFlags,
		Subcommands: []cli.Command{
			{
				Name:        "sethost",
				Usage:       "set host address",
				Action:      setHost,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "hoststring",
				Description: `set host address`,
			},
			{
				Name:        "setcount",
				Usage:       "set count",
				Action:      setCount,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set count`,
			},
			{
				Name:        "settimeout",
				Usage:       "set timeout",
				Action:      setTimeout,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set timeout`,
			},
			{
				Name:        "setgap",
				Usage:       "set gap",
				Action:      setGap,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set gap`,
			},
			{
				Name:        "setopen",
				Usage:       "set open or not",
				Action:      setOpen,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "bool",
				Description: `set open or nor`,
			},
			{
				Name:        "showconfigs",
				Usage:       "show configs in contract",
				Action:      showConfigs,
				Flags:       flags.GeneralFlags,
				Description: `show configs in contract`,
			},
		},
	}
)

func setHost(ctx *cli.Context) error {
	ntw, opts, client := createContractInstanceAndTransactor(ctx, true)
	host := utils.GetFirstStringArgument(ctx)
	tx, err := ntw.UpdateHost(opts, host)
	utils.WaitMined(client, tx, err)
	return nil
}

func setCount(ctx *cli.Context) error {
	ntw, opts, client := createContractInstanceAndTransactor(ctx, true)
	count := utils.GetFirstIntArgument(ctx)
	tx, err := ntw.UpdateCount(opts, big.NewInt(count))
	utils.WaitMined(client, tx, err)
	return nil
}

func setTimeout(ctx *cli.Context) error {
	ntw, opts, client := createContractInstanceAndTransactor(ctx, true)
	timeout := utils.GetFirstIntArgument(ctx)
	tx, err := ntw.UpdateTimeout(opts, big.NewInt(timeout))
	utils.WaitMined(client, tx, err)
	return nil
}

func setGap(ctx *cli.Context) error {
	ntw, opts, client := createContractInstanceAndTransactor(ctx, true)
	gap := utils.GetFirstIntArgument(ctx)
	tx, err := ntw.UpdateGap(opts, big.NewInt(gap))
	utils.WaitMined(client, tx, err)
	return nil
}

func setOpen(ctx *cli.Context) error {
	ntw, opts, client := createContractInstanceAndTransactor(ctx, true)
	open := utils.GetFirstBoolArgument(ctx)
	tx, err := ntw.UpdateOpen(opts, open)
	utils.WaitMined(client, tx, err)
	return nil
}

func showConfigs(ctx *cli.Context) error {
	ntw, _, _ := createContractInstanceAndTransactor(ctx, false)

	host, err := ntw.Host(nil)
	if err != nil {
		log.Fatal("Failed to get host", "err", err)
	}
	log.Info("host", "value", host)

	count, err := ntw.Count(nil)
	if err != nil {
		log.Fatal("Failed to get count", "err", err)
	}
	log.Info("count", "value", count.Int64())

	timeout, err := ntw.Timeout(nil)
	if err != nil {
		log.Fatal("Failed to get timeout", "err", err)
	}
	log.Info("timeout", "value", timeout.Int64())

	gap, err := ntw.Gap(nil)
	if err != nil {
		log.Fatal("Failed to get gap", "err", err)
	}
	log.Info("gap", "value", gap.Int64())

	open, err := ntw.Open(nil)
	if err != nil {
		log.Fatal("Failed to get open", "err", err)
	}
	log.Info("open", "value", open)

	return nil
}

func createContractInstanceAndTransactor(ctx *cli.Context, withTransactor bool) (contract *network.Network, opts *bind.TransactOpts, client *cpclient.Client) {
	contractAddr, client, key := utils.PrepareAll(ctx, withTransactor)

	if withTransactor {
		opts = bind.NewKeyedTransactor(key.PrivateKey)
	}

	contract, err := network.NewNetwork(contractAddr, client)
	if err != nil {
		log.Fatal("Failed to create new contract instance", "err", err)
	}

	return contract, opts, client
}
