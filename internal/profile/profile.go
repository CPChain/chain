package profile

import (
	"runtime"

	"github.com/urfave/cli"
)

type profileConfig struct {
	memProfileRate          int
	blockProfileRate        int
	traceFileName           string
	cpuFileName             string
	blockingProfileFileName string
	memProfileFileName      string
	pprofAddr               string
}

func getDefaultProfileConfig() profileConfig {
	return profileConfig{
		memProfileRate:          runtime.MemProfileRate,
		blockProfileRate:        1,
		traceFileName:           "cpchain-trace.trace",
		cpuFileName:             "cpchain-cpu.profile",
		blockingProfileFileName: "cpchain-block.profile",
		memProfileFileName:      "cpchain-heap.profile",
		pprofAddr:               "localhost:8931",
	}
}

// Start profiling
func Start(ctx *cli.Context) error {
	// start profiling, tracing
	cfg := getDefaultProfileConfig()

	// enable tracing by default
	if err := Handler.StartGoTrace(cfg.traceFileName); err != nil {
		return err
	}

	if err := Handler.StartCPUProfile(cfg.cpuFileName); err != nil {
		return err
	}

	if err := Handler.StartMemProfile(cfg.memProfileRate, cfg.memProfileFileName); err != nil {
		return err
	}

	if err := Handler.StartBlockingProfile(cfg.blockProfileRate, cfg.blockingProfileFileName); err != nil {
		return err
	}

	// pprof server
	StartPProfWebUi(cfg.pprofAddr)
	return nil
}

// Stops all running profiles, flushing their output to the respective file.
func Stop() {
	Handler.StopBlockingProfile()
	Handler.StopMemHeapProfile()
	Handler.StopCPUProfile()
	Handler.StopGoTrace()
}
