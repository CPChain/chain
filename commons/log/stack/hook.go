package stack

import (
	"fmt"
	"os"
	"regexp"
	"runtime/debug"
	"strings"

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

	lines := strings.Split(string(debug.Stack()), "\n")
	idx := 0
	// find the first non-logrus pair
	for idx = 0; idx < (len(lines)-1)/2; idx++ {
		s := lines[1+2*idx]
		if matched, _ := regexp.MatchString("logrus|commons/log|debug\\.Stack", s); !matched {
			break
		}
	}
	lines = append(lines[:1], lines[idx*2+1:]...)
	output := strings.Join(lines, "\n")
	// TODO print to the handler, not stderr
	_, _ = fmt.Fprintln(os.Stderr, output)
	return nil
}
