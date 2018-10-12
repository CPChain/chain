package log

import (
	"os"
	"testing"
)

func TestLoggerDebug(t *testing.T) {
	l := New("module", "test")
	l.SetOutput(os.Stdout)
	// l.Debug("key", 3, "name", "test")
	l.Debug("home", "name", 4)
}
