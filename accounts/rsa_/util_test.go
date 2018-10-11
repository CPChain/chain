package rsa_

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestLoadFile(t *testing.T) {
	bytes, err := LoadFile("/_30mbkeaetmp/notexist")
	assert.Nil(t, bytes)
	assert.NotNil(t, err)
}
