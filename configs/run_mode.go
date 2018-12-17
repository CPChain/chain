// Copyright 2018 The cphain authors

package configs

import (
	"errors"

	"bitbucket.org/cpchain/chain/commons/log"
)

const (
	Dev     = "dev"
	Testnet = "testnet"
	Mainnet = "mainnet"
)

var DefaultRunMode = Dev

// Run mode for switch node configuration, eg:dev|Testnet|prod
var runModeValue = DefaultRunMode

func GetRunMode() string {
	return runModeValue
}

func SetRunMode(runMode string) error {
	if len(runMode) == 0 {
		runModeValue = DefaultRunMode
	} else {
		switch runMode {
		case Dev:
		case Mainnet:
		case Testnet:
		default:
			log.Error("unknown runModeValue", "runModeValue", runMode)
			return errors.New("unknown runModeValue" + runMode)
		}
		runModeValue = runMode
	}
	log.Debug("init runModeValue", "runModeValue", runModeValue)
	return nil
}

func IsDev() bool {
	return Dev == runModeValue
}

func IsMainnet() bool {
	return Mainnet == runModeValue
}

func IsTestnet() bool {
	return Testnet == runModeValue
}
