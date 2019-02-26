package output

import (
	"fmt"
	"os"
	"text/template"

	"bitbucket.org/cpchain/chain/commons/log"
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

// Balance of account
func (l *LogOutput) Balance(balance *cm.Balance) {
	outTmpl := `--------------------------

Balance: {{.Balance}}

Reward:
	Total:  {{.Total}}
	Free:   {{.Free}}
	Locked: {{.Locked}}

--------------------------
`
	tmpl, err := template.New("balance").Parse(outTmpl)
	if err != nil {
		l.Error(err.Error())
	}
	err = tmpl.Execute(os.Stdout, _balance{
		balance.Balance.String(),
		balance.Reward.TotalBalance.String(),
		balance.Reward.FreeBalance.String(),
		balance.Reward.LockedBalance.String(),
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
