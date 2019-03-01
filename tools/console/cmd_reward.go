package main

import (
	"math/big"
	"strconv"

	"bitbucket.org/cpchain/chain/configs"

	"github.com/urfave/cli"
)

var rewardCommand cli.Command

func init() {
	rewardFlags := append([]cli.Flag(nil), GasFlags...)
	rewardCommand = cli.Command{
		Name:  "reward",
		Flags: wrapperFlags(rewardFlags),
		Usage: "Reward contract operations",
		Subcommands: []cli.Command{
			{
				Name:        "deposit",
				Usage:       "Deposit money to fundraising account",
				Flags:       wrapperFlags(rewardFlags),
				Description: "Deposit money to fundraising account. If argument is not present, deposit default 1000 CPC.",
				ArgsUsage:   "[money to deposit]",
				Action:      deposit,
			},
			{
				Name:        "withdraw",
				Usage:       "Withdraw money from fundraising account",
				Flags:       wrapperFlags(rewardFlags),
				Description: "Withdraw money from fundraising account. If argument is not present, withdraw all money in the fundraising account.",
				ArgsUsage:   "[money to withdraw]",

				Action: withdraw,
			},
			{
				Name:   "wantrenew",
				Flags:  wrapperFlags(rewardFlags),
				Usage:  "Confirm to renew the current investment",
				Action: wantRenew,
			},
			{
				Name:   "quitrenew",
				Flags:  wrapperFlags(rewardFlags),
				Usage:  "Confirm to cancel renewing the current investment",
				Action: quitRenew,
			},
		},
	}
}

func deposit(ctx *cli.Context) error {
	console, out, cancel := build(ctx)
	defer cancel()

	if len(ctx.Args()) > 1 {
		out.Fatal("Too many arguments.")
	}

	var value uint64 = 1000
	if len(ctx.Args()) == 1 {
		v, err := strconv.Atoi(ctx.Args().First())
		if err != nil {
			out.Fatal("Argument is illegal", "error", err)
		}
		value = uint64(v)
	} else {
		out.Info("Argument is not present, use default value, 1000 CPC")
	}

	err := console.SubmitDeposit(new(big.Int).Mul(new(big.Int).SetUint64(value), big.NewInt(configs.Cpc)))
	if err != nil {
		out.Error(err.Error())
	}
	return nil
}

func withdraw(ctx *cli.Context) error {
	console, out, cancel := build(ctx)
	defer cancel()

	if len(ctx.Args()) > 1 {
		out.Fatal("Too many arguments.")
	}

	var value *big.Int
	if len(ctx.Args()) == 1 {
		v, err := strconv.Atoi(ctx.Args().First())
		if err != nil {
			out.Fatal("Argument is illegal", "error", err)
		}
		value = new(big.Int).Mul(big.NewInt(int64(v)), big.NewInt(configs.Cpc))
	} else {
		b, err := console.GetBalanceOnReward()
		if err != nil {
			out.Fatal("Encounter error", "error", err)
		}
		value = b.FreeBalance
		out.Info("Argument is not present, use default value, the balance of fundraising account", "value", value)
	}

	err := console.Withdraw(value)
	if err != nil {
		out.Fatal(err.Error())
	}
	return nil
}

func wantRenew(ctx *cli.Context) error {
	console, out, cancel := build(ctx)
	defer cancel()
	err := console.WantRenew()
	if err != nil {
		out.Error(err.Error())
	}
	return nil
}

func quitRenew(ctx *cli.Context) error {
	console, out, cancel := build(ctx)
	defer cancel()
	err := console.QuitRenew()
	if err != nil {
		out.Error(err.Error())
	}
	return nil
}
