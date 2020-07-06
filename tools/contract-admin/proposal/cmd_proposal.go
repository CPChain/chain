package proposal

import (
	"context"
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/contracts/dpor/proposal"
	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"bitbucket.org/cpchain/chain/tools/contract-admin/utils"
	"github.com/ethereum/go-ethereum/common"
	"github.com/urfave/cli"
)

var submitFlag = []cli.Flag{
	cli.StringFlag{
		Name:  "id",
		Usage: "proposal id",
	},
	cli.IntFlag{
		Name:  "period",
		Usage: "period, seconds",
	},
}

var idFlag = []cli.Flag{
	cli.StringFlag{
		Name:  "id",
		Usage: "proposal id",
	},
}

var (
	ProposalCommand = cli.Command{
		Name:  "proposal",
		Usage: "Manage Proposal Contract",
		Description: `
		Manage Proposal Contract
		`,
		Flags: flags.GeneralFlags,
		Subcommands: []cli.Command{
			{
				Name:        "deploy",
				Usage:       "proposal deploy <congress address>",
				Action:      deploy,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "string",
				Description: `deploy contract`,
			},
			{
				Name:        "submit",
				Usage:       "submit --id <id>  --period <period, seconds>",
				Action:      submit,
				Flags:       append(flags.GeneralFlags, submitFlag...),
				Description: `submit proposal`,
			},
			{
				Name:        "approve",
				Usage:       "approve <id>",
				Action:      approve,
				Flags:       flags.GeneralFlags,
				Description: `approve proposal`,
			},
			{
				Name:        "vote",
				Usage:       "vote <id>",
				Action:      vote,
				Flags:       flags.GeneralFlags,
				Description: `vote proposal`,
			},
			{
				Name:        "get-status",
				Usage:       "get-status <id>",
				Action:      getStatus,
				Flags:       flags.GeneralFlags,
				Description: `status of proposal`,
			},
			{
				Name:        "show-configs",
				Usage:       "proposal showconfigs",
				Action:      showConfigs,
				Flags:       flags.GeneralFlags,
				Description: `show configs`,
			},
			{
				Name:        "set-amount-threshold",
				Usage:       "set-amount-threshold <value>",
				Action:      setAmountThreshold,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set amount threshold`,
			},
			{
				Name:        "set-approval-threshold",
				Usage:       "set-approval-threshold <value>",
				Action:      setApprovalThreshold,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set approval threshold`,
			},
			{
				Name:        "set-vote-threshold",
				Usage:       "set-vote-threshold <value>",
				Action:      setVoteThreshold,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set vote threshold`,
			},
			{
				Name:        "set-min-congress",
				Usage:       "set-min-congress <value>",
				Action:      setMinCongress,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set vote threshold`,
			},
			{
				Name:        "set-id-length",
				Usage:       "set-id-length <value>",
				Action:      setIDLength,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set IDLength`,
			},
			{
				Name:        "set-max-period",
				Usage:       "set-max-period <value>",
				Action:      setMaxPeriod,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set maxPeriod`,
			},
			{
				Name:        "disable",
				Usage:       "disbale",
				Action:      disable,
				Flags:       flags.GeneralFlags,
				Description: `disable contract`,
			},
			{
				Name:        "enable",
				Usage:       "enable",
				Action:      enable,
				Flags:       flags.GeneralFlags,
				Description: `enable contract`,
			},
			{
				Name:        "refund",
				Usage:       "refund --id <proposal id>",
				Action:      refund,
				Flags:       append(flags.GeneralFlags, idFlag...),
				Description: `refund`,
			},
			{
				Name:        "refund-all",
				Usage:       "refund-all",
				Action:      refundAll,
				Flags:       flags.GeneralFlags,
				Description: `refund all`,
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

	congressAddr := utils.GetFirstStringArgument(ctx)
	addr, tx, _, err := proposal.DeployProposal(auth, client, common.HexToAddress(congressAddr))
	if err != nil {
		log.Fatal("deploy proposal contract error", "err", err)
	}
	log.Info("proposal contract address", "addr", addr.Hex())
	return utils.WaitMined(client, tx)
}

func submit(ctx *cli.Context) error {
	id := ctx.String("id")
	period := ctx.Int("period")
	log.Info("submit proposal", "id", id, "period", period)
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	amountThreshold, err := instance.AmountThreshold(nil)
	if err != nil {
		return err
	}
	opts.Value = amountThreshold
	tx, err := instance.Submit(opts, id, big.NewInt(int64(period)))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func approve(ctx *cli.Context) error {
	id := utils.GetFirstStringArgument(ctx)
	log.Info("approve proposal", "id", id)
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	tx, err := instance.Approval(opts, id)
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func vote(ctx *cli.Context) error {
	id := utils.GetFirstStringArgument(ctx)
	log.Info("vote proposal", "id", id)
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	tx, err := instance.Vote(opts, id)
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func getStatus(ctx *cli.Context) error {
	id := utils.GetFirstStringArgument(ctx)
	log.Info("proposal", "id", id)
	instance, _, _, err := createContractInstanceAndTransactor(ctx, false)
	if err != nil {
		return err
	}
	if status, err := instance.GetStatus(nil, id); err != nil {
		return err
	} else {
		switch status {
		case 0:
			log.Info("Deposited")
		case 1:
			log.Info("Approved")
		case 2:
			log.Info("Successful")
		case 3:
			log.Info("Timeout")
		}
	}
	return nil
}

func showConfigs(ctx *cli.Context) error {
	instance, _, _, err := createContractInstanceAndTransactor(ctx, false)
	if err != nil {
		return err
	}
	if _, err := instance.GetCongressNum(nil); err != nil {
		log.Error("Maybe your congress contract address is wrong, please check it.")
		return err
	}

	enabled, _ := instance.Enabled(nil)
	log.Info("contract enabled", "value", enabled)

	amountThreshold, _ := instance.AmountThreshold(nil)
	log.Info("amount threshold", "value", amountThreshold, "cpc", big.NewInt(0).Div(amountThreshold, big.NewInt(configs.Cpc)))

	approvalThreshold, _ := instance.ApprovalThreshold(nil)
	log.Info("approval threshold", "value", approvalThreshold)

	voteThreshold, _ := instance.VoteThreshold(nil)
	log.Info("vote threshold", "value", voteThreshold)

	minCongress, _ := instance.MinCongressMemberCount(nil)
	log.Info("min member of congress", "value", minCongress)

	IDLength, _ := instance.IdLength(nil)
	log.Info("max length of ID", "value", IDLength)

	maxPeriod, _ := instance.MaxPeriod(nil)
	log.Info("max value of period", "value", maxPeriod, "days", big.NewInt(0).Div(maxPeriod, big.NewInt(24*60*60)))

	return nil
}

func setAmountThreshold(ctx *cli.Context) error {
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	value := utils.GetFirstIntArgument(ctx)
	log.Info("set amount threshold", "value", value)
	tx, err := instance.SetAmountThreshold(opts, big.NewInt(value))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setApprovalThreshold(ctx *cli.Context) error {
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	value := utils.GetFirstIntArgument(ctx)
	log.Info("set approval threshold", "value", value)
	tx, err := instance.SetApprovalThreshold(opts, big.NewInt(value))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setVoteThreshold(ctx *cli.Context) error {
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	value := utils.GetFirstIntArgument(ctx)
	log.Info("set vote threshold", "value", value)
	tx, err := instance.SetVoteThreshold(opts, uint16(value))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setMinCongress(ctx *cli.Context) error {
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	value := utils.GetFirstIntArgument(ctx)
	log.Info("set min member count of congress", "value", value)
	tx, err := instance.SetMinCongressMemberCount(opts, uint16(value))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setIDLength(ctx *cli.Context) error {
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	value := utils.GetFirstIntArgument(ctx)
	log.Info("set vote threshold", "value", value)
	tx, err := instance.SetIDLength(opts, uint16(value))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func setMaxPeriod(ctx *cli.Context) error {
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	value := utils.GetFirstIntArgument(ctx)
	log.Info("set vote threshold", "value", value)
	tx, err := instance.SetMaxPeriod(opts, big.NewInt(value))
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func disable(ctx *cli.Context) error {
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	tx, err := instance.DisableContract(opts)
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func enable(ctx *cli.Context) error {
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	tx, err := instance.EnableContract(opts)
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func refund(ctx *cli.Context) error {
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	id := ctx.String("id")
	tx, err := instance.Refund(opts, id)
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func refundAll(ctx *cli.Context) error {
	instance, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	value, _ := client.BalanceAt(context.Background(), opts.From, client.GetBlockNumber())
	log.Info("balance", "value", value)
	tx, err := instance.RefundAll(opts)
	if err != nil {
		return err
	}
	return utils.WaitMined(client, tx)
}

func createContractInstanceAndTransactor(ctx *cli.Context, withTransactor bool) (contract *proposal.Proposal, opts *bind.TransactOpts, client *cpclient.Client, err error) {
	contractAddr, client, key, err := utils.PrepareAll(ctx, withTransactor)
	if err != nil {
		return &proposal.Proposal{}, &bind.TransactOpts{}, &cpclient.Client{}, err
	}
	if withTransactor {
		opts = bind.NewKeyedTransactor(key.PrivateKey)
	}

	contract, err = proposal.NewProposal(contractAddr, client)
	if err != nil {
		log.Info("Failed to create new contract instance", "err", err)
		return &proposal.Proposal{}, &bind.TransactOpts{}, &cpclient.Client{}, err
	}

	return contract, opts, client, nil
}
