package main

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestIsInvalidAddress(t *testing.T) {
	assert.Equal(t, isInvalidAddress("e94b7b6c5a0e526a4d97f9768ad6097bde25c62a"), false)
	assert.Equal(t, isInvalidAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"), false)
	assert.Equal(t, isInvalidAddress("0e94b7b6c5a0e526a4d97f9768ad6097bde25c62a"), true)
	assert.Equal(t, isInvalidAddress("1e94b7b6c5a0e526a4d97f9768ad6097bde25c62a"), true)
}
