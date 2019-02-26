package manager

import (
	"context"
	"testing"

	out "bitbucket.org/cpchain/chain/tools/console/output"
)

func TestManager(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	endPoint := "http://54.169.196.149:8503"
	kspath := "/Users/liaojinlong/.cpchain/keystore/"
	password := "/Users/liaojinlong/.cpchain/password"

	output := out.NewLogOutput()

	manager := NewConsole(&ctx, endPoint, kspath, password, &output)

	manager.GetStatus()
}
