package congress

import (
	"errors"
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/congress"
	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"bitbucket.org/cpchain/chain/tools/contract-admin/utils"
	"github.com/ethereum/go-ethereum/common"
	"github.com/urfave/cli"
)

var (
	CongressCommand = cli.Command{
		Name:  "congress",
		Usage: "Manage Congress Contract",
		Description: `
		Manage Congress Contract
		`,
		Flags: flags.GeneralFlags,
		Subcommands: []cli.Command{
			{
				Name:        "deploy",
				Usage:       "deploy contract",
				Action:      deploy,
				Flags:       flags.GeneralFlags,
				Description: `deploy contract`,
			},
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
				Name:        "isincongress",
				Usage:       "is in congress",
				Action:      isInCongress,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "address",
				Description: `check an address is in congress`,
			},
			{
				Name:        "showconfigs",
				Usage:       "show configs in contract",
				Action:      showConfigs,
				Flags:       flags.GeneralFlags,
				Description: `show configs in contract`,
			},
			{
				Name:        "showcongress",
				Usage:       "show congress's members in contract",
				Action:      showCongress,
				Flags:       flags.GeneralFlags,
				Description: `show congress in contract`,
			},
			{
				Name:        "join",
				Usage:       "join congress",
				Action:      join,
				Flags:       flags.GeneralFlags,
				Description: `join congress`,
			},
			{
				Name:        "quit",
				Usage:       "quit congress",
				Action:      quit,
				Flags:       flags.GeneralFlags,
				Description: `quit congress`,
			},
		},
	}
)

func deploy(ctx *cli.Context) error {
	endpoint, err := flags.GetEndpoint(ctx)
	if err != nil {
		log.Fatal("endpoint error", "err", err)
	}
	client, err := utils.PrepareCpclient(endpoint)
	if err != nil {
		log.Fatal("prepare client error", "err", err)
	}
	_ = client
	keystoreFile, err := flags.GetKeystorePath(ctx)
	if err != nil {
		log.Fatal("get keystore path error", "err", err)
	}
	password := utils.GetPassword()
	_, key := utils.GetAddressAndKey(keystoreFile, password)
	auth := bind.NewKeyedTransactor(key.PrivateKey)
	_ = auth
	addr, tx, _, err := congress.DeployCongress(auth, client)
	if err != nil {
		log.Fatal("deploy congress contract error", "err", err)
	}
	log.Info("congress contract address", "addr", addr.Hex())
	return utils.WaitMined(client, tx)
}

func setThreshold(ctx *cli.Context) error {
	congress, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	thresholdStr := utils.GetFirstStringArgument(ctx)
	threshold := new(big.Int)
	threshold, ok := threshold.SetString(thresholdStr, 10)
	if !ok {
		log.Info("Failed to parse string to big int", "string", thresholdStr)
		return errors.New("Failed to parse string to big int" + " string " + thresholdStr)
	}

	tx, err := congress.SetCongressThreshold(opts, threshold)
	if err != nil {
		log.Error("set congress threshold error", "err", err)
		return err
	}
	return utils.WaitMined(client, tx)
}

func setPeriod(ctx *cli.Context) error {
	congress, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	period := utils.GetFirstIntArgument(ctx)
	tx, err := congress.SetPeriod(opts, big.NewInt(period))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setVersion(ctx *cli.Context) error {
	congress, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	version := utils.GetFirstIntArgument(ctx)
	tx, err := congress.SetSupportedVersion(opts, big.NewInt(version))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func refund(ctx *cli.Context) error {
	congress, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	addr := utils.GetFirstStringArgument(ctx)
	tx, err := congress.Refund(opts, common.HexToAddress(addr))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func refundAll(ctx *cli.Context) error {
	congress, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	tx, err := congress.RefundAll(opts)
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func disable(ctx *cli.Context) error {
	congress, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	tx, err := congress.DisableContract(opts)
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func isInCongress(ctx *cli.Context) error {
	congress, _, _, err := createContractInstanceAndTransactor(ctx, false)
	if err != nil {
		return err
	}
	addr := utils.GetFirstStringArgument(ctx)
	isInCongress, err := congress.IsInCongress(nil, common.HexToAddress(addr))
	if err != nil {
		log.Info("Failed to get isInCongress info", "err", err, "addr", addr)
		return err
	}
	log.Info("isInCongress", "bool", isInCongress)

	return nil
}

func showConfigs(ctx *cli.Context) error {
	congress, _, _, err := createContractInstanceAndTransactor(ctx, false)
	if err != nil {
		return err
	}
	period, err := congress.Period(nil)
	if err != nil {
		log.Info("Failed to get period", "err", err)
		return err
	}
	log.Info("period", "value", period.Int64())

	version, err := congress.SupportedVersion(nil)
	if err != nil {
		log.Info("Failed to get version", "err", err)
		return err
	}
	log.Info("version", "value", version.Int64())

	threshold, err := congress.CongressThreshold(nil)
	if err != nil {
		log.Info("Failed to get threshold", "err", err)
		return err
	}
	log.Info("threshold", "value", threshold)
	return nil
}

func showCongress(ctx *cli.Context) error {
	congress, _, _, err := createContractInstanceAndTransactor(ctx, false)
	if err != nil {
		return err
	}
	members, err := congress.GetCongress(nil)
	if err != nil {
		log.Info("Failed to get congress", "err", err)
		return err
	}
	log.Info("congress's members len", "value", len(members))

	for _, r := range members {
		log.Info("congress member", "addr", r.Hex())
	}

	return nil
}

func join(ctx *cli.Context) error {
	congress, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	utils.PrintBalance(client, opts.From)
	version, err := congress.SupportedVersion(nil)
	if err != nil {
		log.Info("Failed to get version", "err", err)
		return err
	}
	threshold, err := congress.CongressThreshold(nil)
	if err != nil {
		log.Info("Failed to get threshold", "err", err)
		return err
	}
	opts.Value = threshold
	tx, err := congress.JoinCongress(opts, version)
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func quit(ctx *cli.Context) error {
	congress, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	tx, err := congress.QuitCongress(opts)
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func createContractInstanceAndTransactor(ctx *cli.Context, withTransactor bool) (contract *congress.Congress, opts *bind.TransactOpts, client *cpclient.Client, err error) {
	contractAddr, client, key, err := utils.PrepareAll(ctx, withTransactor)
	if err != nil {
		return &congress.Congress{}, &bind.TransactOpts{}, &cpclient.Client{}, err
	}
	if withTransactor {
		opts = bind.NewKeyedTransactor(key.PrivateKey)
	}

	contract, err = congress.NewCongress(contractAddr, client)
	if err != nil {
		log.Info("Failed to create new contract instance", "err", err)
		return &congress.Congress{}, &bind.TransactOpts{}, &cpclient.Client{}, err
	}

	return contract, opts, client, nil
}
