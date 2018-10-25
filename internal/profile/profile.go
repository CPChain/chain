package profile

import (
	"path"
	"runtime"

	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
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

func getProfileConfig(ctx *cli.Context) profileConfig {
	dirPath := ""
	if ctx.IsSet(flags.ProfileFlagName) {
		dirPath = ctx.String(flags.ProfileFlagName)
	}
	return profileConfig{
		memProfileRate:          runtime.MemProfileRate,
		blockProfileRate:        1,
		traceFileName:           path.Join(dirPath, "cpchain-trace.trace"),
		cpuFileName:             path.Join(dirPath, "cpchain-cpu.profile"),
		blockingProfileFileName: path.Join(dirPath, "cpchain-block.profile"),
		memProfileFileName:      path.Join(dirPath, "cpchain-heap.profile"),
		pprofAddr:               "localhost:8931",
	}
}

// Start profiling
func Start(ctx *cli.Context) error {
	// start profiling, tracing
	cfg := getProfileConfig(ctx)

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
