package api

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
