package output

import (
	"testing"
)

func TestLogOutput(t *testing.T) {
	output := NewLogOutput()
	output.Info("Info")
	output.Error("Error")
	output.Warn("Warn")

}
