package main

import (
	"os"
	"fmt"
	"math/big"
	"text/template"

	"github.com/urfave/cli"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/tools/reward-admin/common"
)

var statusCommand cli.Command

func init() {
	statusFlags := append([]cli.Flag(nil))
	statusCommand = cli.Command{
		Action: ShowStatus,
		Name:   "status",
		Flags:  wrapperFlags(statusFlags),
		Usage:  "Show status of user",
	}
}

func ShowStatus(ctx *cli.Context) error {
	admin, out, cancel := Build(ctx)
	defer cancel()
	investorList, err := admin.GetInvestorList(ctx)
	if err != nil {
		out.Error(err.Error())
	}
	fmt.Println("---- Reward Status Overview ----")
	length := len(investorList)
	for i := 0; i < length; i++ {
		m := investorList[i]
		PrintInvestorItem(&m)
	}
	fmt.Println()
	fmt.Printf("Lock Status: %v \t\t Total Locked Amount: %s CPC \n", admin.IsLocked(), convert(admin.TotalInvestorsAmount()))
	fmt.Printf("Contract Balance: %s CPC \n", convert(admin.ContractAccountBalance()))
	return nil
}

// Balance of account
func PrintInvestorItem(message *common.InvestorInfo) {
	if message.FreeBalance == nil {
		message.FreeBalance = big.NewInt(0)
	}
	if message.LockedBalance == nil {
		message.LockedBalance = big.NewInt(0)
	}

	outTmpl := "Account:  {{.Account}}  \t  Fundraising:   {{.Free}} CPC \t  Locked: {{.Locked}} CPC  \t  Renew: {{.ToRenew}}\n"
	tmpl, err := template.New("Account").Parse(outTmpl)
	if err != nil {
		log.Error(err.Error())
	}
	err = tmpl.Execute(os.Stdout, _useritem{

		convert(message.FreeBalance),
		convert(message.LockedBalance),
		message.IsToRenew,
		message.Account.Hex(),
	})

	if err != nil {
		log.Error(err.Error())
	}
}

type _useritem struct {
	Free    string
	Locked  string
	ToRenew bool
	Account string
}

func convert(val *big.Int) string {
	_val := new(big.Float).SetInt(val)
	return new(big.Float).Quo(_val, big.NewFloat(configs.Cpc)).String()
}
