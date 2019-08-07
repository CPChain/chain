// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package config

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestSetConfigErrDirNotFound(t *testing.T) {
	err := SetConfig("", "./testkey00")
	assert.NotNil(t, err)
	assert.Equal(t, ErrDirNotFound, err)

}

func TestSetConfigErrNoKeyFound(t *testing.T) {
	t.Skip("unable create empty dir in git")
	err := SetConfig("", "./testkey0")
	assert.NotNil(t, err)
	assert.Equal(t, ErrNoKeyFound, err)

}

func TestSetConfigOk(t *testing.T) {
	err := SetConfig("", "./testkey1")
	assert.Nil(t, err)
}

func TestSetConfigErrMoreThanOneKeyFound(t *testing.T) {
	err := SetConfig("", "./testkey2")
	assert.NotNil(t, err)
	assert.Equal(t, ErrMoreThanOneKeyFound, err)
}

func TestSetConfigErrNotDir(t *testing.T) {
	err := SetConfig("", "./testkey1/key1")
	assert.NotNil(t, err)
	assert.Equal(t, ErrNotDir, err)
}
