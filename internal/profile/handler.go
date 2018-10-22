// Copyright 2016 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

// Package debug interfaces Go runtime debugging facilities.
// This package is mostly glue code making these facilities available
// through the CLI and RPC subsystem. If you want to use them from Go code,
// use package runtime instead.
package profile

import (
	"errors"
	"fmt"
	"io"
	"net/http"
	_ "net/http/pprof"
	"os"
	"runtime"
	"runtime/pprof"
	"runtime/trace"
	"sync"

	"bitbucket.org/cpchain/chain/commons/log"
)

// Handler is the global debugging handler.
var Handler = new(HandlerT)

var (
	ProfilingNotInProgressError = errors.New("CPU profiling not in progress")
	BlockProfileNotExistError   = errors.New("Block profile does not exist")
)

type profilingDumpError struct {
	profile string
	error   error
}

func (df *profilingDumpError) Error() string {
	return fmt.Sprintf("Dumping %s profile failed. %s", df.profile, df.error.Error())
}

// HandlerT implements the debugging API.
// Do not create values of this type, use the one
// in the Handler variable instead.
type HandlerT struct {
	mu           sync.Mutex
	cpuW         io.WriteCloser
	cpuFile      string
	memW         io.WriteCloser
	memFile      string
	blockingW    io.WriteCloser
	blockingFile string
	traceW       io.WriteCloser
	traceFile    string
}

// MemStats returns detailed runtime memory statistics.
func (*HandlerT) MemStats() *runtime.MemStats {
	s := new(runtime.MemStats)
	runtime.ReadMemStats(s)
	return s
}

// StartCPUProfile turns on CPU profiling, writing to the given file.
func (h *HandlerT) StartCPUProfile(file string) error {
	h.mu.Lock()
	defer h.mu.Unlock()
	if h.cpuW != nil {
		return errors.New("CPU profiling already in progress")
	}
	f, err := os.Create(file)
	if err != nil {
		return err
	}
	if err := pprof.StartCPUProfile(f); err != nil {
		f.Close()
		return err
	}
	h.cpuW = f
	h.cpuFile = file
	log.Info("CPU profiling started", "dump", h.cpuFile)
	return nil
}

// StopCPUProfile stops an ongoing CPU profile.
func (h *HandlerT) StopCPUProfile() error {
	h.mu.Lock()
	defer h.mu.Unlock()
	pprof.StopCPUProfile()
	if h.cpuW == nil {
		return ProfilingNotInProgressError
	}
	log.Info("Done writing CPU profile", "dump", h.cpuFile)
	h.cpuW.Close()
	h.cpuW = nil
	h.cpuFile = ""

	return nil
}

func writeBlockProfile(writer io.WriteCloser) error {
	p := pprof.Lookup("block")
	if p != nil {
		return p.WriteTo(writer, 0)
	} else {
		return BlockProfileNotExistError
	}
}

// tracing
// StartGoTrace turns on tracing, writing to the given file.
func (h *HandlerT) StartGoTrace(file string) error {
	h.mu.Lock()
	defer h.mu.Unlock()
	if h.traceW != nil {
		return errors.New("trace already in progress")
	}
	f, err := os.Create(file)
	if err != nil {
		return err
	}
	if err := trace.Start(f); err != nil {
		f.Close()
		return err
	}
	h.traceW = f
	h.traceFile = file
	log.Info("Go tracing started", "dump", h.traceFile)
	return nil
}

// StopTrace stops an ongoing trace.
func (h *HandlerT) StopGoTrace() error {
	h.mu.Lock()
	defer h.mu.Unlock()
	trace.Stop()
	if h.traceW == nil {
		return errors.New("trace not in progress")
	}
	log.Info("Done writing Go trace", "dump", h.traceFile)
	h.traceW.Close()
	h.traceW = nil
	h.traceFile = ""
	return nil
}

// StartBlockingProfile starts blocking profiling.
// rate 0 disables block profiling.
func (h *HandlerT) StartBlockingProfile(rate int, file string) error {
	h.mu.Lock()
	defer h.mu.Unlock()

	if h.blockingW != nil {
		return errors.New("Blocking profiling already in progress")
	}
	f, err := os.Create(file)
	if err != nil {
		return err
	}
	h.blockingFile = file
	h.blockingW = f

	runtime.SetBlockProfileRate(rate)
	return nil
}

// StopBlockProfile stops an ongoing blocking profile
func (h *HandlerT) StopBlockingProfile() error {
	if h.blockingW == nil {
		return ProfilingNotInProgressError
	}
	if err := writeBlockProfile(h.blockingW); err == nil {
		log.Info("Done writing blocking profile", "dump", h.blockingFile)
	} else {
		return &profilingDumpError{"block", err}
	}

	h.blockingW.Close()
	h.blockingW = nil
	h.blockingFile = ""

	runtime.SetBlockProfileRate(0)

	return nil
}

// StartMemProfile starts the memory profiling rate that controls the fraction of memory allocations
// that are recorded and reported in the memory profile.
func (h *HandlerT) StartMemProfile(rate int, file string) error {
	h.mu.Lock()
	defer h.mu.Unlock()

	if h.memW != nil {
		return errors.New("Memory heap profiling already in progress")
	}
	f, err := os.Create(file)
	if err != nil {
		return err
	}
	h.memFile = file
	h.memW = f

	runtime.MemProfileRate = rate
	return nil
}

// StopMemHeapProfile stops an ongoing memory heap profile
func (h *HandlerT) StopMemHeapProfile() error {
	if h.memW == nil {
		return ProfilingNotInProgressError
	}
	if error := pprof.WriteHeapProfile(h.memW); error == nil {
		log.Info("Done writing memory heap profile", "dump", h.memFile)
	} else {
		return &profilingDumpError{"heap", error}
	}
	h.memW.Close()
	h.memW = nil
	h.memFile = ""

	runtime.MemProfileRate = 0
	return nil
}

func StartPProfWebUi(address string) {
	log.Info("Starting pprof server", "addr", fmt.Sprintf("http://%s/debug/pprof", address))
	go func() {
		if err := http.ListenAndServe(address, nil); err != nil {
			log.Error("Failure in running pprof server", "err", err)
		}
	}()
}
