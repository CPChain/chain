// Copyright 2018 The cpchain authors
package configs

import "bitbucket.org/cpchain/chain/commons/log"

var CpchainValidators = []string{
	"enode://9826a2f72c63eaca9b7f57b169473686f5a133dc24ffac858b4e5185a5eb60b144a414c35359585d9ea9d67f6fcca29578f9e002c89e94cc4bcc46a2b336c166@127.0.0.1:30317",
	"enode://7ce9c4fee12b12affbbe769a0faaa6e256bbae3374717fb94e1fb4be308fae3795c3abae023a587d8e14b35d278bd3d10916117bb8b3f5cfa4c951c5d56eeed7@127.0.0.1:30318",
	"enode://1db32421dc881357c282091960fdbd13f3635f8e3f87a953b6d9c429e53469727018bd0bb02da48acc4f1b4bec946b8f158705262b37163b4ab321a1c932d8f9@127.0.0.1:30319",
	"enode://fd0f365cec4e052040151f2a4a9ba23e8592acd3cacfdc4af2e8b6dbc6fb6b25ca088151889b19729d02c48e390de9682b316db2351636fdd1ee5ea1cd32bf46@127.0.0.1:30320",
}

var defaultValidators = []string{}

func GetDefaultValidators() []string {
	return defaultValidators
}

func InitDefaultValidators(validators []string) {
	if validators == nil || len(validators) == 0 {
		defaultValidators = CpchainValidators
	} else {
		defaultValidators = validators
	}
	log.Debug("init validators", "nodes", defaultValidators)
}
