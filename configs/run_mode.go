// Copyright 2018 The cphain authors

package configs

import (
	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/pkg/errors"
)

// Run mode for switch node configuration, eg:dev|testnet|prod
var runModeValue = DefaultRunMode

var DefaultRunMode = "dev"

func GetRunMode() string {
	return runModeValue
}

func SetRunMode(runMode string) error {
	if len(runMode) == 0 {
		runModeValue = DefaultRunMode
	} else {
		switch runMode {
		case "dev":
		case "prod":
		case "testnet":
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
	return "dev" == runModeValue
}

func IsProd() bool {
	return "prod" == runModeValue
}

func IsTestnet() bool {
	return "testnet" == runModeValue
}
