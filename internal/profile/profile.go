package profile

import (
	"runtime"

	"github.com/urfave/cli"
)

type profileConfig struct {
	memProfileRate   int
	blockProfileRate int
	traceFileName    string
	cpuFileName      string
	pprofAddr        string
}

var defaultProfileConfig = profileConfig{
	memProfileRate:   runtime.MemProfileRate,
	blockProfileRate: 1,
	traceFileName:    "~/.cpchain/dev-trace",
	cpuFileName:      "~/.cpchain/dev-cpu",
	pprofAddr:        "localhost:8931",
}

// Start profiling
func Start(ctx *cli.Context) error {
	// profiling, tracing
	cfg := defaultProfileConfig
	// currently, we ignore the ctx flags

	runtime.MemProfileRate = cfg.memProfileRate
	Handler.SetBlockProfileRate(cfg.blockProfileRate)

	// enable tracing by default
	if err := Handler.StartGoTrace(cfg.traceFileName); err != nil {
		return err
	}

	if err := Handler.StartCPUProfile(cfg.cpuFileName); err != nil {
		return err
	}

	// pprof server
	StartPProf(cfg.pprofAddr)
	return nil
}

// Stops all running profiles, flushing their output to the respective file.
func Stop() {
	Handler.StopCPUProfile()
	Handler.StopGoTrace()
}

