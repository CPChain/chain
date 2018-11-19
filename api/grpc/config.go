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

package grpc

import (
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"strings"
)

const (
	defaultHost        = "localhost"
	defaultPort        = 8544
	defaultJsonRpcHost = "localhost"
	defaultJsonRpcPort = 8543
)

// Config grpc configuration
type Config struct {
	Modules []string `toml:",omitempty"`
	DataDir string   `toml:",omitempt"`
	Host    string   `toml:",omitempty"`
	Port    int      `toml:",omitempty"`

	JsonRpcHost string `toml:",omitempty"`
	JsonRpcPort int    `toml:",omitempty"`

	IpcPath string `toml:",omitempty"`
}

// Address returns the grpc server address
func (c *Config) Address() string {
	if c.Host == "" {
		c.Host = defaultHost
	}
	if c.Port == 0 {
		c.Port = defaultPort
	}
	return fmt.Sprintf("%s:%d", c.Host, c.Port)
}

// JsonHttpAddress returns the restfull json http server address
func (c *Config) JsonHttpAddress() string {
	if c.JsonRpcHost == "" {
		c.JsonRpcHost = defaultJsonRpcHost
	}
	if c.JsonRpcPort == 0 {
		c.JsonRpcPort = defaultJsonRpcPort
	}
	return fmt.Sprintf("%s:%d", c.JsonRpcHost, c.JsonRpcPort)
}

// IpcAddress returns the ipc server address
func (c *Config) IpcAddress() string {
	// Short circuit if IPC has not been enabled
	if c.IpcPath == "" {
		return ""
	}
	// On windows we can only use plain top-level pipes
	if runtime.GOOS == "windows" {
		if strings.HasPrefix(c.IpcPath, `\\.\pipe\`) {
			return c.IpcPath
		}
		return `\\.\pipe\` + c.IpcPath
	}
	// Resolve names into the data directory full paths otherwise
	if filepath.Base(c.IpcPath) == c.IpcPath {
		if c.DataDir == "" {
			return filepath.Join(os.TempDir(), c.IpcPath)
		}
		return filepath.Join(c.DataDir, c.IpcPath)
	}
	return c.IpcPath
}
