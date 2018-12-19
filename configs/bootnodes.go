// Copyright 2018 The cpchain authors

package configs

func Bootnodes() []string {
	if IsDev() {
		return devBootnodes
	}
	if IsTestnet() {
		return testnetBootnodes
	}
	if IsMainnet() {
		return mainnetBootnodes
	}
	return devBootnodes
}
