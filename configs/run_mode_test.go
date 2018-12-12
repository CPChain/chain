// Copyright 2018 The cphain authors

package configs

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestSetRunModeToDev(t *testing.T) {
	SetRunMode("dev")
	runMode := GetRunMode()
	assert.Equal(t, "dev", runMode)
	assert.Equal(t, true, IsDev())
}

func TestSetRunModeToProd(t *testing.T) {
	SetRunMode("prod")
	runMode := GetRunMode()
	assert.Equal(t, "prod", runMode)
	assert.Equal(t, true, IsProd())
	SetRunMode("dev")
}

func TestSetRunModeToTestnet(t *testing.T) {
	SetRunMode("testnet")
	runMode := GetRunMode()
	assert.Equal(t, "testnet", runMode)
	assert.Equal(t, true, IsTestnet())
	SetRunMode("dev")
}

func TestSetRunModeToUnknown(t *testing.T) {
	err := SetRunMode("Unknown")
	if err == nil {
		t.Error("set Unknown runmode should be error")
	}
	SetRunMode("dev")
}

func TestSetRunModeToNil(t *testing.T) {
	SetRunMode("")
	assert.Equal(t, "dev", runModeValue)
	assert.Equal(t, true, IsDev())
}
