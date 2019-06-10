// Copyright 2018 The cphain authors

package configs

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestSetRunModeToDev(t *testing.T) {
	SetRunMode(Dev)
	runMode := GetRunMode()
	assert.Equal(t, Dev, runMode)
	assert.Equal(t, true, IsDev())
}

func TestSetRunModeToProd(t *testing.T) {
	SetRunMode(Mainnet)
	runMode := GetRunMode()
	assert.Equal(t, Mainnet, runMode)
	assert.Equal(t, true, IsMainnet())
	SetRunMode(Dev)
}

func TestSetRunModeToTestnet(t *testing.T) {
	SetRunMode(Testnet)
	runMode := GetRunMode()
	assert.Equal(t, Testnet, runMode)
	assert.Equal(t, true, IsTestnet())
	SetRunMode(Dev)
}

func TestSetRunModeToUnknown(t *testing.T) {
	err := SetRunMode("Unknown")
	if err == nil {
		t.Error("set Unknown runmode should be error")
	}
	SetRunMode(Dev)
}

func TestSetRunModeToNil(t *testing.T) {
	SetRunMode("")
	assert.Equal(t, Dev, runModeValue)
	assert.Equal(t, true, IsDev())
}

func TestString(t *testing.T) {
	SetRunMode(Testnet)
	assert.Equal(t, "testnet", runModeValue.String())
}
