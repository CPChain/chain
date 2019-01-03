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
	profileAddress := "localhost:8931"
	if ctx.IsSet(flags.ProfileAddressFlagName) {
		profileAddress = ctx.String(flags.ProfileAddressFlagName)
	}
	return profileConfig{
		memProfileRate:          runtime.MemProfileRate,
		blockProfileRate:        1,
		traceFileName:           path.Join(dirPath, "cpchain-trace.trace"),
		cpuFileName:             path.Join(dirPath, "cpchain-cpu.profile"),
		blockingProfileFileName: path.Join(dirPath, "cpchain-block.profile"),
		memProfileFileName:      path.Join(dirPath, "cpchain-heap.profile"),
		pprofAddr:               profileAddress,
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
