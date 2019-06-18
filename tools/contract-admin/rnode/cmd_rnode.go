package rnode

import (
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/rnode"
	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"bitbucket.org/cpchain/chain/tools/contract-admin/utils"
	"github.com/ethereum/go-ethereum/common"
	"github.com/urfave/cli"
)

var (
	RnodeCommand = cli.Command{
		Name:  "rnode",
		Usage: "Manage Rnode Contract",
		Description: `
		Manage Rnode Contract
		`,
		Flags: flags.GeneralFlags,
		Subcommands: []cli.Command{
			{
				Name:        "setthreshold",
				Usage:       "set threshold ",
				Action:      setThreshold,
				Flags:       flags.GeneralFlags,
				Description: `set threshold`,
			},
			{
				Name:        "setperiod",
				Usage:       "set period",
				Action:      setPeriod,
				Flags:       flags.GeneralFlags,
				Description: `set period`,
			},
			{
				Name:        "setversion",
				Usage:       "set version",
				Action:      setVersion,
				Flags:       flags.GeneralFlags,
				Description: `set version`,
			},
			{
				Name:        "refund",
				Usage:       "refund",
				Action:      refund,
				Flags:       flags.GeneralFlags,
				Description: `refund`,
			},
			{
				Name:        "refundall",
				Usage:       "refund all",
				Action:      refundAll,
				Flags:       flags.GeneralFlags,
				Description: `refund all`,
			},
			{
				Name:        "disable",
				Usage:       "disable rnode contract",
				Action:      disable,
				Flags:       flags.GeneralFlags,
				Description: `disable rnode contract`,
			},
			{
				Name:        "isrnode",
				Usage:       "is rnode",
				Action:      isRnode,
				Flags:       flags.GeneralFlags,
				Description: `check an address is rnode`,
			},
			{
				Name:        "showconfigs",
				Usage:       "show configs in contract",
				Action:      showConfigs,
				Flags:       flags.GeneralFlags,
				Description: `show configs in contract`,
			},
			{
				Name:        "showrnodes",
				Usage:       "show rnodes in contract",
				Action:      showConfigs,
				Flags:       flags.GeneralFlags,
				Description: `show rnodes in contract`,
			},
		},
	}
)

func setThreshold(ctx *cli.Context) error {
	rnd, opts := createContractInstanceAndTransactor(ctx, true)
	thresholdStr := utils.GetFirstStringArgument(ctx)
	threshold := new(big.Int)
	threshold, ok := threshold.SetString(thresholdStr, 10)
	if !ok {
		log.Fatal("Failed to parse string to big int", "string", thresholdStr)
	}

	_, err := rnd.SetRnodeThreshold(opts, threshold)
	if err != nil {
		log.Fatal("Failed to update", "err", err)
	}

	log.Info("Successfully updated")

	return nil
}

func setPeriod(ctx *cli.Context) error {
	rnd, opts := createContractInstanceAndTransactor(ctx, true)
	period := utils.GetFirstUintArgument(ctx)
	_, err := rnd.SetPeriod(opts, big.NewInt(period))
	if err != nil {
		log.Fatal("Failed to update", "err", err)
	}

	log.Info("Successfully updated")

	return nil
}

func setVersion(ctx *cli.Context) error {
	rnd, opts := createContractInstanceAndTransactor(ctx, true)
	version := utils.GetFirstUintArgument(ctx)
	_, err := rnd.SetSupportedVersion(opts, big.NewInt(version))
	if err != nil {
		log.Fatal("Failed to update", "err", err)
	}

	log.Info("Successfully updated")

	return nil
}

func refund(ctx *cli.Context) error {
	rnd, opts := createContractInstanceAndTransactor(ctx, true)
	addr := utils.GetFirstStringArgument(ctx)
	_, err := rnd.Refund(opts, common.HexToAddress(addr))
	if err != nil {
		log.Fatal("Failed to update", "err", err)
	}

	log.Info("Successfully updated")

	return nil
}

func refundAll(ctx *cli.Context) error {
	rnd, opts := createContractInstanceAndTransactor(ctx, true)
	_, err := rnd.RefundAll(opts)
	if err != nil {
		log.Fatal("Failed to update", "err", err)
	}

	log.Info("Successfully updated")

	return nil
}

func disable(ctx *cli.Context) error {
	rnd, opts := createContractInstanceAndTransactor(ctx, true)
	_, err := rnd.DisableContract(opts)
	if err != nil {
		log.Fatal("Failed to update", "err", err)
	}

	log.Info("Successfully updated")

	return nil
}

func isRnode(ctx *cli.Context) error {
	rnd, _ := createContractInstanceAndTransactor(ctx, false)
	addr := utils.GetFirstStringArgument(ctx)
	_, err := rnd.IsRnode(nil, common.HexToAddress(addr))
	if err != nil {
		log.Fatal("Failed to update", "err", err)
	}

	log.Info("Successfully updated")

	return nil
}

func showConfigs(ctx *cli.Context) error {
	rnd, _ := createContractInstanceAndTransactor(ctx, false)

	period, err := rnd.Period(nil)
	if err != nil {
		log.Fatal("Failed to get period", "err", err)
	}
	log.Info("period", "value", period.Int64())

	version, err := rnd.SupportedVersion(nil)
	if err != nil {
		log.Fatal("Failed to get version", "err", err)
	}
	log.Info("version", "value", version.Int64())

	threshold, err := rnd.RnodeThreshold(nil)
	if err != nil {
		log.Fatal("Failed to get threshold", "err", err)
	}
	log.Info("threshold", "value", threshold)

	return nil
}

func showRnodes(ctx *cli.Context) error {
	rnd, _ := createContractInstanceAndTransactor(ctx, false)

	rnodes, err := rnd.GetRnodes(nil)
	if err != nil {
		log.Fatal("Failed to get rnodes", "err", err)
	}
	log.Info("rnode len", "value", len(rnodes))

	for _, r := range rnodes {
		log.Info("rnode", "addr", r.Hex())
	}

	return nil
}

func createContractInstanceAndTransactor(ctx *cli.Context, withTransactor bool) (contract *rnode.Rnode, opts *bind.TransactOpts) {
	contractAddr, client, key := utils.PrepareAll(ctx, withTransactor)

	if withTransactor {
		opts = bind.NewKeyedTransactor(key.PrivateKey)
	}

	contract, err := rnode.NewRnode(contractAddr, client)
	if err != nil {
		log.Fatal("Failed to create new contract instance", "err", err)
	}

	return contract, opts
}
