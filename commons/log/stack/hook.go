package stack

import (
	"runtime/debug"

	"github.com/sirupsen/logrus"
)

var fieldName = "stacktrace"

type StackHook struct{}

func NewHook() StackHook {
	return StackHook{}
}

// Levels provides the levels to filter.
func (hook StackHook) Levels() []logrus.Level {
	return []logrus.Level{logrus.PanicLevel, logrus.FatalLevel, logrus.ErrorLevel}
}

// Fire is called by logrus when something is logged.
func (hook StackHook) Fire(entry *logrus.Entry) error {
	// st := string(debug.Stack())
	// entry.Data[fieldName] = st
	// entry.Data["foo"] = "bar\n\bar"

	// we just print stack to stderr.  because entry.Data quotes the newline, so the message is cluttered.
	// cf. https://github.com/sirupsen/logrus/issues/654

	// TODO
	debug.PrintStack()
	return nil
}
