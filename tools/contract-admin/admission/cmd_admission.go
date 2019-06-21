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
	adm, opts, client := createContractInstanceAndTransactor(ctx, true)
	difficulty := utils.GetFirstIntArgument(ctx)
	tx, err := adm.UpdateCPUDifficulty(opts, big.NewInt(difficulty))
	utils.WaitMined(client, tx, err)
	return nil
}

func setMemDifficulty(ctx *cli.Context) error {
	adm, opts, client := createContractInstanceAndTransactor(ctx, true)
	difficulty := utils.GetFirstIntArgument(ctx)
	tx, err := adm.UpdateMemoryDifficulty(opts, big.NewInt(difficulty))
	utils.WaitMined(client, tx, err)
	return nil
}

func showDifficulties(ctx *cli.Context) error {
	adm, _, _ := createContractInstanceAndTransactor(ctx, false)

	cpuDifficulty, err := adm.CpuDifficulty(nil)
	if err != nil {
		log.Fatal("Failed to get cpu difficulty", "err", err)
	}
	log.Info("CPU difficulty", "value", cpuDifficulty.Int64())

	memDifficulty, err := adm.MemoryDifficulty(nil)
	if err != nil {
		log.Fatal("Failed to get memory difficulty", "err", err)
	}
	log.Info("Mem difficulty", "value", memDifficulty.Int64())

	return nil
}

func createContractInstanceAndTransactor(ctx *cli.Context, withTransactor bool) (contract *admission.Admission, opts *bind.TransactOpts, client *cpclient.Client) {
	contractAddr, client, key := utils.PrepareAll(ctx, withTransactor)

	if withTransactor {
		opts = bind.NewKeyedTransactor(key.PrivateKey)
	}
	contract, err := admission.NewAdmission(contractAddr, client)
	if err != nil {
		log.Fatal("Failed to create new contract instance", "err", err)
	}

	return contract, opts, client
}
