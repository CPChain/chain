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
	defaultGatewayHost = "localhost"
	defaultGatewayPort = 8543
)

// Config grpc configuration
type Config struct {
	Modules []string `toml:",omitempty"`
	DataDir string   `toml:",omitempt"`
	Host    string   `toml:",omitempty"`
	Port    int      `toml:",omitempty"`

	GatewayHost string `toml:",omitempty"`
	GatewayPort int    `toml:",omitempty"`

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

// GatewayAddress returns the restfull json http server address
func (c *Config) GatewayAddress() string {
	if c.GatewayHost == "" {
		c.GatewayHost = defaultGatewayHost
	}
	if c.GatewayPort == 0 {
		c.GatewayPort = defaultGatewayPort
	}
	return fmt.Sprintf("%s:%d", c.GatewayHost, c.GatewayPort)
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
