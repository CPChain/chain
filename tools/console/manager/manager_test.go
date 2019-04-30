package manager

import (
	"context"
	"testing"

	out "bitbucket.org/cpchain/chain/tools/console/output"
)

func TestManager(t *testing.T) {
	t.Skip()
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	endPoint := "http://127.0.0.1:8503"
	kspath := "/Users/liaojinlong/.cpchain/keystore/"
	password := "/Users/liaojinlong/.cpchain/password"
	output := out.NewLogOutput()

	manager, _ := NewConsole(&ctx, endPoint, kspath, password, &output)

	manager.GetStatus()
}
