package output

import (
	cm "bitbucket.org/cpchain/chain/tools/console/common"
)

// LogOutput output data in log
type LogOutput struct {
}

// NewLogOutput new a object
func NewLogOutput() LogOutput {
	return LogOutput{}
}

// Status shows the status of node
func (l *LogOutput) Status(status *cm.Status) {

}

// Balance of account
func (l *LogOutput) Balance(balance cm.Balance) {

}

// Info log
func (l *LogOutput) Info(info string) {

}

// Error log
func (l *LogOutput) Error(err string) {

}

// Fatal log
func (l *LogOutput) Fatal(fatal string) {

}

// Warn log
func (l *LogOutput) Warn(warn string) {

}
