package output

import (
	"fmt"
	"math/big"
	"os"
	"text/template"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	cm "bitbucket.org/cpchain/chain/tools/console/common"
)

// LogOutput output data in log
type LogOutput struct {
	logger *log.Logger
}

// NewLogOutput new a object
func NewLogOutput() LogOutput {
	logger := log.New()
	return LogOutput{logger}
}

// Status shows the status of node
func (l *LogOutput) Status(status *cm.Status) {
	outTmpl := `--------------------------

Mining: {{.Mining}}

RNode: {{.RNode}}

Proposer: {{.Proposer}}
	`
	if status.Proposer {
		outTmpl += `
NextNumber: {{.NextNumber}}
	`
	}
	outTmpl += `
--------------------------
`

	tmpl, err := template.New("status").Parse(outTmpl)
	if err != nil {
		l.Error(err.Error())
	}
	err = tmpl.Execute(os.Stdout, status)
	if err != nil {
		l.Error(err.Error())
	}
	fmt.Println()
}

type _balance struct {
	Balance string
	Total   string
	Free    string
	Locked  string
}

func convert(val *big.Int) string {
	_val := new(big.Float).SetInt(val)
	return new(big.Float).Quo(_val, big.NewFloat(configs.Cpc)).String()
}

// Balance of account
func (l *LogOutput) Balance(balance *cm.Balance) {
	outTmpl := `--------------------------

Balance: {{.Balance}} CPC

Reward:
	Total:  {{.Total}} CPC
	Free:   {{.Free}} CPC
	Locked: {{.Locked}} CPC

--------------------------
`
	tmpl, err := template.New("balance").Parse(outTmpl)
	if err != nil {
		l.Error(err.Error())
	}
	err = tmpl.Execute(os.Stdout, _balance{
		convert(&balance.Balance),
		convert(&balance.Reward.TotalBalance),
		convert(&balance.Reward.FreeBalance),
		convert(&balance.Reward.LockedBalance),
	})
	if err != nil {
		l.Error(err.Error())
	}
}

// Info log
func (l *LogOutput) Info(msg string, params ...interface{}) {
	l.logger.Info(msg, params...)
}

// Error log
func (l *LogOutput) Error(msg string, params ...interface{}) {
	l.logger.Error(msg, params...)
}

// Fatal log
func (l *LogOutput) Fatal(msg string, params ...interface{}) {
	l.logger.Fatal(msg, params...)
}

// Warn log
func (l *LogOutput) Warn(msg string, params ...interface{}) {
	l.logger.Warn(msg, params...)
}
