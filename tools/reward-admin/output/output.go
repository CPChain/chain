package output

import (
	"bitbucket.org/cpchain/chain/commons/log"
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
