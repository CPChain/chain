package rpt

import (
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	rptContract "bitbucket.org/cpchain/chain/contracts/dpor/rpt"
	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"bitbucket.org/cpchain/chain/tools/contract-admin/utils"
	"github.com/urfave/cli"
)

var (
	RptCommand = cli.Command{
		Name:  "rpt",
		Usage: "Manage Rpt Contract",
		Description: `
		Manage Rpt Contract
		`,
		Flags: flags.GeneralFlags,
		Subcommands: []cli.Command{
			{
				Name:        "setlowrptpct",
				Usage:       "set low rpt percentage",
				Action:      setLowRptPercentage,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set low rpt percentage`,
			},
			{
				Name:        "settotalseats",
				Usage:       "set total seats",
				Action:      setTotalSeats,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set total seats`,
			},
			{
				Name:        "setlowrptseats",
				Usage:       "set low rpt seats",
				Action:      setLowRptSeats,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set low rpt seats`,
			},
			{
				Name:        "setwindow",
				Usage:       "set window",
				Action:      setWindow,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set window`,
			},
			{
				Name:        "setalpha",
				Usage:       "set alpha",
				Action:      setAlpha,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set alpha`,
			},
			{
				Name:        "setbeta",
				Usage:       "set beta",
				Action:      setBeta,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set beta`,
			},
			{
				Name:        "setgamma",
				Usage:       "set gamma",
				Action:      setGamma,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set gamma`,
			},
			{
				Name:        "setpsi",
				Usage:       "set psi",
				Action:      setPsi,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set psi`,
			},
			{
				Name:        "setomega",
				Usage:       "set omega",
				Action:      setOmega,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set omega`,
			},
			{
				Name:        "showconfigs",
				Usage:       "show configs in contract",
				Action:      showConfigs,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `show configs in contract`,
			},
		},
	}
)

func setLowRptPercentage(ctx *cli.Context) error {
	rpt, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	pct := utils.GetFirstIntArgument(ctx)
	tx, err := rpt.UpdateLowRptPercentage(opts, big.NewInt(pct))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setTotalSeats(ctx *cli.Context) error {
	rpt, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	seats := utils.GetFirstIntArgument(ctx)
	tx, err := rpt.UpdateTotalSeats(opts, big.NewInt(seats))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setLowRptSeats(ctx *cli.Context) error {
	rpt, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}

	seats := utils.GetFirstIntArgument(ctx)
	tx, err := rpt.UpdateLowRptSeats(opts, big.NewInt(seats))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setWindow(ctx *cli.Context) error {
	rpt, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	window := utils.GetFirstIntArgument(ctx)
	tx, err := rpt.UpdateWindow(opts, big.NewInt(window))
	if err != nil {
		return err
	}

	return utils.WaitMined(client, tx)
}

func setAlpha(ctx *cli.Context) error {
	rpt, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	alpha := utils.GetFirstIntArgument(ctx)
	tx, err := rpt.UpdateAlpha(opts, big.NewInt(alpha))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setBeta(ctx *cli.Context) error {
	rpt, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}

	beta := utils.GetFirstIntArgument(ctx)
	tx, err := rpt.UpdateBeta(opts, big.NewInt(beta))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setGamma(ctx *cli.Context) error {
	rpt, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}

	gamma := utils.GetFirstIntArgument(ctx)
	tx, err := rpt.UpdateGamma(opts, big.NewInt(gamma))
	if err != nil {
		return err
	}

	return utils.WaitMined(client, tx)
}

func setPsi(ctx *cli.Context) error {
	rpt, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}

	psi := utils.GetFirstIntArgument(ctx)
	tx, err := rpt.UpdatePsi(opts, big.NewInt(psi))
	if err != nil {
		return err
	}

	return utils.WaitMined(client, tx)
}

func setOmega(ctx *cli.Context) error {
	rpt, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}

	omega := utils.GetFirstIntArgument(ctx)
	tx, err := rpt.UpdateOmega(opts, big.NewInt(omega))
	if err != nil {
		return err
	}

	return utils.WaitMined(client, tx)
}

func showConfigs(ctx *cli.Context) error {
	rpt, _, _, err := createContractInstanceAndTransactor(ctx, false)
	if err != nil {
		return err
	}

	lowPct, err := rpt.LowRptPercentage(nil)
	if err != nil {
		log.Fatal("Failed to get low rpt percentage", "err", err)
	}
	log.Info("low rpt percentage", "value", lowPct.Int64())

	lowSeats, err := rpt.LowRptSeats(nil)
	if err != nil {
		log.Fatal("Failed to get low rpt seats", "err", err)
	}
	log.Info("low rpt seats", "value", lowSeats.Int64())

	totalSeats, err := rpt.TotalSeats(nil)
	if err != nil {
		log.Fatal("Failed to get total seats", "err", err)
	}
	log.Info("total seats", "value", totalSeats.Int64())

	window, err := rpt.Window(nil)
	if err != nil {
		log.Fatal("Failed to get window len", "err", err)
	}
	log.Info("window len", "value", window.Int64())

	alpha, err := rpt.Alpha(nil)
	if err != nil {
		log.Fatal("Failed to get alpha", "err", err)
	}
	log.Info("alpha", "value", alpha.Int64())

	beta, err := rpt.Beta(nil)
	if err != nil {
		log.Fatal("Failed to get beta", "err", err)
	}
	log.Info("beta", "value", beta.Int64())

	gamma, err := rpt.Gamma(nil)
	if err != nil {
		log.Fatal("Failed to get gamma", "err", err)
	}
	log.Info("gamma", "value", gamma.Int64())

	psi, err := rpt.Psi(nil)
	if err != nil {
		log.Fatal("Failed to get psi", "err", err)
	}
	log.Info("psi", "value", psi.Int64())

	omega, err := rpt.Omega(nil)
	if err != nil {
		log.Fatal("Failed to get omega", "err", err)
	}
	log.Info("omega", "value", omega.Int64())

	return nil
}

func createContractInstanceAndTransactor(ctx *cli.Context, withTransactor bool) (contract *rptContract.Rpt, opts *bind.TransactOpts, client *cpclient.Client, err error) {
	contractAddr, client, key, err := utils.PrepareAll(ctx, withTransactor)
	if err != nil {
		return &rptContract.Rpt{}, &bind.TransactOpts{}, &cpclient.Client{}, err
	}

	if withTransactor {
		opts = bind.NewKeyedTransactor(key.PrivateKey)
	}

	contract, err = rptContract.NewRpt(contractAddr, client)
	if err != nil {
		log.Info("Failed to create new contract instance", "err", err)
		return &rptContract.Rpt{}, &bind.TransactOpts{}, &cpclient.Client{}, err
	}

	return contract, opts, client, nil
}
