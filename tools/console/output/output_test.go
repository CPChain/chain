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
		Balance: *big.NewInt(200000000000000),
		Reward: status.RewardBalance{
			TotalBalance:  big.NewInt(0),
			FreeBalance:   big.NewInt(0),
			LockedBalance: big.NewInt(0),
		},
	})

	// Status
	output.Status(&status.Status{
		Mining:     true,
		RNode:      true,
		ENode:      true,
		Proposer:   true,
		Locked:     true,
		NextNumber: big.NewInt(100),
	})
	output.Status(&status.Status{
		Mining:     true,
		RNode:      true,
		ENode:      true,
		Proposer:   false,
		Locked:     true,
		NextNumber: big.NewInt(100),
	})
}
