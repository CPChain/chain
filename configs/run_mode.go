// Copyright 2018 The cphain authors

package configs

import (
	"fmt"

	"bitbucket.org/cpchain/chain/commons/log"
)

type RunMode string

const (
	Dev         RunMode = "dev"
	Testnet     RunMode = "testnet"
	Mainnet     RunMode = "mainnet"
	TestMainnet RunMode = "testmainnet"
	Testcase    RunMode = "testcase"
)

// Run mode for switch node configuration, eg:dev|testnet|mainnet
var runModeValue = Mainnet

func GetRunMode() RunMode {
	return runModeValue
}

func SetRunMode(runMode RunMode) error {
	switch runMode {
	case Dev:
	case Mainnet:
	case TestMainnet:
	case Testnet:
	case Testcase:
	default:
		log.Error(fmt.Sprintf("unknown runModeValue, revert to default mode: %s", runModeValue), "runModeValue", runMode)
		return fmt.Errorf("unknown runModeValue %s", runMode)
	}
	runModeValue = runMode
	log.Debug("init runModeValue", "runModeValue", runModeValue)
	return nil
}

func IsDev() bool {
	return Dev == runModeValue
}

func IsMainnet() bool {
	return Mainnet == runModeValue
}

func IsTestMainnet() bool {
	return TestMainnet == runModeValue
}

func IsTestnet() bool {
	return Testnet == runModeValue
}

func IsTestcase() bool {
	return Testcase == runModeValue
}
