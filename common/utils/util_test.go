package utils

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestLoadFile(t *testing.T) {
	bytes, err := LoadFile("/tmp/notexist")
	assert.Nil(t, bytes)
	assert.NotNil(t, err)
}
