// Copyright 2018 The cpchain authors

package configs

func Bootnodes() []string {
	switch {
	case IsDev():
		return devBootnodes
	case IsTestnet():
		return testnetBootnodes
	case IsMainnet():
		return mainnetBootnodes
	default:
		return devBootnodes
	}
}
