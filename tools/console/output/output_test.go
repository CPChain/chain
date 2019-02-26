package output

import (
	"math/big"
	"testing"

	status "bitbucket.org/cpchain/chain/tools/console/common"
)

func TestLogOutput(t *testing.T) {
	output := NewLogOutput()
	output.Info("Info")
	output.Error("Error")
	output.Warn("Warn")

	// Balance
	output.Balance(&status.Balance{
		*big.NewInt(200000000000000),
		status.RewardBalance{
			*big.NewInt(0),
			*big.NewInt(0),
			*big.NewInt(0),
		},
	})

	// Status
	output.Status(&status.Status{
		true,
		true,
		true,
		true,
		big.NewInt(100),
	})
	output.Status(&status.Status{
		true,
		true,
		true,
		false,
		big.NewInt(0),
	})
}
