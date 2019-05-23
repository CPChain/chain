package output

import (
	"testing"

	status "bitbucket.org/cpchain/chain/tools/console/common"
)

func TestLogOutput(t *testing.T) {
	output := NewLogOutput()
	output.Info("Info")
	output.Error("Error")
	output.Warn("Warn")
	
	// Status
	output.Status(&status.Status{
		Mining:     true,
		RNode:      true,
		Proposer:   true,
	})
	output.Status(&status.Status{
		Mining:     true,
		RNode:      true,
		Proposer:   false,
	})
}
