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
	ntw, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	host := utils.GetFirstStringArgument(ctx)
	tx, err := ntw.UpdateHost(opts, host)
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setCount(ctx *cli.Context) error {
	ntw, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	count := utils.GetFirstIntArgument(ctx)
	tx, err := ntw.UpdateCount(opts, big.NewInt(count))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setTimeout(ctx *cli.Context) error {
	ntw, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	timeout := utils.GetFirstIntArgument(ctx)
	tx, err := ntw.UpdateTimeout(opts, big.NewInt(timeout))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setGap(ctx *cli.Context) error {
	ntw, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	gap := utils.GetFirstIntArgument(ctx)
	tx, err := ntw.UpdateGap(opts, big.NewInt(gap))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setOpen(ctx *cli.Context) error {
	ntw, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	open := utils.GetFirstBoolArgument(ctx)
	tx, err := ntw.UpdateOpen(opts, open)
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func showConfigs(ctx *cli.Context) error {
	ntw, _, _, err := createContractInstanceAndTransactor(ctx, false)
	if err != nil {
		return err
	}

	host, err := ntw.Host(nil)
	if err != nil {
		log.Info("Failed to get host", "err", err)
		return err
	}
	log.Info("host", "value", host)

	count, err := ntw.Count(nil)
	if err != nil {
		log.Info("Failed to get count", "err", err)
		return err
	}
	log.Info("count", "value", count.Int64())

	timeout, err := ntw.Timeout(nil)
	if err != nil {
		log.Info("Failed to get timeout", "err", err)
		return err
	}
	log.Info("timeout", "value", timeout.Int64())

	gap, err := ntw.Gap(nil)
	if err != nil {
		log.Info("Failed to get gap", "err", err)
		return err
	}
	log.Info("gap", "value", gap.Int64())

	open, err := ntw.Open(nil)
	if err != nil {
		log.Info("Failed to get open", "err", err)
		return err
	}
	log.Info("open", "value", open)

	return nil
}

func createContractInstanceAndTransactor(ctx *cli.Context, withTransactor bool) (contract *network.Network, opts *bind.TransactOpts, client *cpclient.Client, err error) {
	contractAddr, client, key, err := utils.PrepareAll(ctx, withTransactor)
	if err != nil {
		return &network.Network{}, &bind.TransactOpts{}, &cpclient.Client{}, err
	}
	if withTransactor {
		opts = bind.NewKeyedTransactor(key.PrivateKey)
	}

	contract, err = network.NewNetwork(contractAddr, client)
	if err != nil {
		return &network.Network{}, &bind.TransactOpts{}, &cpclient.Client{}, err
	}

	return contract, opts, client, nil
}
