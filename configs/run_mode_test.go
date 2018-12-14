// Copyright 2018 The cphain authors

package configs

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestSetRunModeToDev(t *testing.T) {
	SetRunMode(DEV)
	runMode := GetRunMode()
	assert.Equal(t, DEV, runMode)
	assert.Equal(t, true, IsDev())
}

func TestSetRunModeToProd(t *testing.T) {
	SetRunMode(MAINNET)
	runMode := GetRunMode()
	assert.Equal(t, MAINNET, runMode)
	assert.Equal(t, true, IsMainnet())
	SetRunMode(DEV)
}

func TestSetRunModeToTestnet(t *testing.T) {
	SetRunMode(TESTNET)
	runMode := GetRunMode()
	assert.Equal(t, TESTNET, runMode)
	assert.Equal(t, true, IsTestnet())
	SetRunMode(DEV)
}

func TestSetRunModeToUnknown(t *testing.T) {
	err := SetRunMode("Unknown")
	if err == nil {
		t.Error("set Unknown runmode should be error")
	}
	SetRunMode(DEV)
}

func TestSetRunModeToNil(t *testing.T) {
	SetRunMode("")
	assert.Equal(t, DEV, runModeValue)
	assert.Equal(t, true, IsDev())
}
