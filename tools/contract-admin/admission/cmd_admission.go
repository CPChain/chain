package admission

import (
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/admission"
	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"bitbucket.org/cpchain/chain/tools/contract-admin/utils"
	"github.com/urfave/cli"
)

var (
	AdmissionCommand = cli.Command{
		Name:  "admission",
		Usage: "Manage Admission Contract",
		Description: `

		Manage Admission Contract
		`,
		Flags: flags.GeneralFlags,
		Subcommands: []cli.Command{
			{
				Name:        "setcpu",
				Usage:       "set cpu difficulty",
				Action:      setCPUDifficulty,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set cpu difficulty`,
			},
			{
				Name:        "setmem",
				Usage:       "set memory difficulty",
				Action:      setMemDifficulty,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set memory difficulty`,
			},
			{
				Name:        "show",
				Usage:       "Show CPU difficulty and memory difficulty",
				Action:      showDifficulties,
				Flags:       flags.GeneralFlags,
				Description: `show cpu difficulty and memory difficulty`,
			},
		},
	}
)

func setCPUDifficulty(ctx *cli.Context) error {
	adm, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		log.Info("Failed to get cpu difficulty", "err", err)
		return err
	}
	difficulty := utils.GetFirstIntArgument(ctx)
	tx, err := adm.UpdateCPUDifficulty(opts, big.NewInt(difficulty))
	if err != nil {
		log.Info("Failed to update cpu difficulty", "err", err)
		return err
	}
	return utils.WaitMined(client, tx)
}

func setMemDifficulty(ctx *cli.Context) error {
	adm, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		log.Info("Failed to get cpu difficulty", "err", err)
		return err
	}
	difficulty := utils.GetFirstIntArgument(ctx)
	tx, err := adm.UpdateMemoryDifficulty(opts, big.NewInt(difficulty))
	if err != nil {
		log.Info("Failed to update memory difficulty", "err", err)
		return err
	}
	return utils.WaitMined(client, tx)
}

func showDifficulties(ctx *cli.Context) error {
	adm, _, _, err := createContractInstanceAndTransactor(ctx, false)
	if err != nil {
		log.Info("Failed to get cpu difficulty", "err", err)
		return err
	}

	cpuDifficulty, err := adm.CpuDifficulty(nil)
	if err != nil {
		log.Info("Failed to get cpu difficulty", "err", err)
		return err
	}
	log.Info("CPU difficulty", "value", cpuDifficulty.Int64())

	memDifficulty, err := adm.MemoryDifficulty(nil)
	if err != nil {
		log.Info("Failed to get memory difficulty", "err", err)
		return err
	}
	log.Info("Mem difficulty", "value", memDifficulty.Int64())
	return nil
}

func createContractInstanceAndTransactor(ctx *cli.Context, withTransactor bool) (contract *admission.Admission, opts *bind.TransactOpts, client *cpclient.Client, err error) {
	contractAddr, client, key, err := utils.PrepareAll(ctx, withTransactor)

	if err != nil {
		log.Info("Failed to create new contract instance", "err", err)
		return &admission.Admission{}, &bind.TransactOpts{}, &cpclient.Client{}, err
	}

	if withTransactor {
		opts = bind.NewKeyedTransactor(key.PrivateKey)
	}
	contract, err = admission.NewAdmission(contractAddr, client)
	if err != nil {
		log.Info("Failed to create new contract instance", "err", err)
		return &admission.Admission{}, &bind.TransactOpts{}, &cpclient.Client{}, err
	}

	return contract, opts, client, nil
}
