package rnode

import (
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
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
				ArgsUsage:   "ValueInWei",
				Description: `set threshold`,
			},
			{
				Name:        "setperiod",
				Usage:       "set period",
				Action:      setPeriod,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set period`,
			},
			{
				Name:        "setversion",
				Usage:       "set version",
				Action:      setVersion,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set version`,
			},
			{
				Name:        "refund",
				Usage:       "refund",
				Action:      refund,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "address",
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
				ArgsUsage:   "address",
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
				Action:      showRnodes,
				Flags:       flags.GeneralFlags,
				Description: `show rnodes in contract`,
			},
		},
	}
)

func setThreshold(ctx *cli.Context) error {
	rnd, opts, client := createContractInstanceAndTransactor(ctx, true)
	thresholdStr := utils.GetFirstStringArgument(ctx)
	threshold := new(big.Int)
	threshold, ok := threshold.SetString(thresholdStr, 10)
	if !ok {
		log.Fatal("Failed to parse string to big int", "string", thresholdStr)
	}

	tx, err := rnd.SetRnodeThreshold(opts, threshold)
	utils.WaitMined(client, tx, err)
	return nil
}

func setPeriod(ctx *cli.Context) error {
	rnd, opts, client := createContractInstanceAndTransactor(ctx, true)
	period := utils.GetFirstIntArgument(ctx)
	tx, err := rnd.SetPeriod(opts, big.NewInt(period))
	utils.WaitMined(client, tx, err)
	return nil
}

func setVersion(ctx *cli.Context) error {
	rnd, opts, client := createContractInstanceAndTransactor(ctx, true)
	version := utils.GetFirstIntArgument(ctx)
	tx, err := rnd.SetSupportedVersion(opts, big.NewInt(version))
	utils.WaitMined(client, tx, err)
	return nil
}

func refund(ctx *cli.Context) error {
	rnd, opts, client := createContractInstanceAndTransactor(ctx, true)
	addr := utils.GetFirstStringArgument(ctx)
	tx, err := rnd.Refund(opts, common.HexToAddress(addr))
	utils.WaitMined(client, tx, err)
	return nil
}

func refundAll(ctx *cli.Context) error {
	rnd, opts, client := createContractInstanceAndTransactor(ctx, true)
	tx, err := rnd.RefundAll(opts)
	utils.WaitMined(client, tx, err)
	return nil
}

func disable(ctx *cli.Context) error {
	rnd, opts, client := createContractInstanceAndTransactor(ctx, true)
	tx, err := rnd.DisableContract(opts)
	utils.WaitMined(client, tx, err)
	return nil
}

func isRnode(ctx *cli.Context) error {
	rnd, _, _ := createContractInstanceAndTransactor(ctx, false)
	addr := utils.GetFirstStringArgument(ctx)
	isRnode, err := rnd.IsRnode(nil, common.HexToAddress(addr))
	if err != nil {
		log.Fatal("Failed to get isRnode info", "err", err, "addr", addr)
	}
	log.Info("IsRnode", "bool", isRnode)

	return nil
}

func showConfigs(ctx *cli.Context) error {
	rnd, _, _ := createContractInstanceAndTransactor(ctx, false)

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
	rnd, _, _ := createContractInstanceAndTransactor(ctx, false)

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

func createContractInstanceAndTransactor(ctx *cli.Context, withTransactor bool) (contract *rnode.Rnode, opts *bind.TransactOpts, client *cpclient.Client) {
	contractAddr, client, key := utils.PrepareAll(ctx, withTransactor)

	if withTransactor {
		opts = bind.NewKeyedTransactor(key.PrivateKey)
	}

	contract, err := rnode.NewRnode(contractAddr, client)
	if err != nil {
		log.Fatal("Failed to create new contract instance", "err", err)
	}

	return contract, opts, client
}
