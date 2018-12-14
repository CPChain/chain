// Copyright 2018 The cphain authors

package configs

import (
	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/pkg/errors"
)

const (
	DEV     = "dev"
	TESTNET = "testnet"
	MAINNET = "mainnet"
)

var DefaultRunMode = DEV

// Run mode for switch node configuration, eg:dev|testnet|prod
var runModeValue = DefaultRunMode

func GetRunMode() string {
	return runModeValue
}

func SetRunMode(runMode string) error {
	if len(runMode) == 0 {
		runModeValue = DefaultRunMode
	} else {
		switch runMode {
		case DEV:
		case MAINNET:
		case TESTNET:
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
	return DEV == runModeValue
}

func IsMainnet() bool {
	return MAINNET == runModeValue
}

func IsTestnet() bool {
	return TESTNET == runModeValue
}
