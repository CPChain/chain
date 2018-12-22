// Copyright 2018 The cpchain authors
package configs

import "bitbucket.org/cpchain/chain/commons/log"

var defaultValidatorNodes []string

func GetDefaultValidators() []string {
	return defaultValidatorNodes
}

func InitDefaultValidators(validators []string) {
	defaultValidatorNodes = defaultDevValidatorNodes
	runMode := GetRunMode()
	switch runMode {
	case Mainnet:
		defaultValidatorNodes = defaultMainnetValidatorNodes
	case Testnet:
		defaultValidatorNodes = defaultTestnetValidatorNodes
	case Dev:
		defaultValidatorNodes = defaultDevValidatorNodes
	}

	if validators != nil && len(validators) > 0 {
		defaultValidatorNodes = validators
	}

	log.Debug("init validators", "nodes", defaultValidatorNodes)
}
