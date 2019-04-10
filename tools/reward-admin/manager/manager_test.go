package manager_test

import (
	"context"
	"testing"

	"bitbucket.org/cpchain/chain/tools/reward-admin/manager"
	out "bitbucket.org/cpchain/chain/tools/reward-admin/output"
)

func TestNewRound(t *testing.T) {
	t.Skip()
	NewRound()
}

func TestNewRaise(t *testing.T) {
	t.Skip()
	NewRaise()
}

func NewRaise() {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	endPoint := "http://127.0.0.1:8501"
	kspath := "../../../examples/cpchain/data/data21/keystore/key21"
	password := "../../../examples/cpchain/conf-dev/passwords/password"

	output := out.NewLogOutput()

	manager := manager.NewConsole(&ctx, endPoint, kspath, password, &output)
	manager.StartNewRaise()

}
func NewRound() {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	endPoint := "http://127.0.0.1:8501"
	kspath := "../../../examples/cpchain/data/data21/keystore/key21"
	password := "../../../examples/cpchain/conf-dev/passwords/password"

	output := out.NewLogOutput()

	manager := manager.NewConsole(&ctx, endPoint, kspath, password, &output)
	manager.SetPeriod()
	manager.StartNewRound()
}
