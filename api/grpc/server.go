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
	"net"
	"net/http"
	"os"
	"path/filepath"

	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

// Server GRpc Server
type Server struct {
	config *Config

	handler *grpc.Server

	gatewayListener net.Listener

	ipcHandler  *grpc.Server
	ipcListener net.Listener

	mux        *runtime.ServeMux
	dialOpts   []grpc.DialOption
	serverOpts []grpc.ServerOption
}

// NewServer creates a new implementation of a Server
func NewServer(dataDir string, modules []string, cfg *Config) *Server {
	// update grpc config
	cfg.DataDir = dataDir
	cfg.Modules = make([]string, 0, len(modules))
	cfg.Modules = append(cfg.Modules, modules...)

	s := &Server{
		config:     cfg,
		mux:        runtime.NewServeMux(),
		serverOpts: []grpc.ServerOption{},
		dialOpts:   []grpc.DialOption{grpc.WithInsecure()},
	}

	return s
}

// Start starts the underlying grpc.Server
func (s *Server) Start() error {
	if err := s.startGrpc(); err != nil {
		return err
	}
	if err := s.startIpc(); err != nil {
		s.stopGrpc()
		return err
	}
	return nil
}

func (s *Server) startGrpc() error {
	s.handler = grpc.NewServer(s.serverOpts...)
	listener, err := net.Listen("tcp", s.config.Address())
	if err != nil {
		log.Error(err.Error())
		return err
	}
	go func(handler *grpc.Server, lis net.Listener) {
		if err := handler.Serve(lis); err != nil {
			// the server could be stopped before its started.
			// this happens when we run TestNodeLifeCycle
			if err != grpc.ErrServerStopped {
				log.Error(err.Error())
			}
		}
	}(s.handler, listener)

	s.gatewayListener, err = net.Listen("tcp", s.config.JsonHttpAddress())
	if err != nil {
		log.Error(err.Error())
		return err
	}
	go func(lis net.Listener, mux *runtime.ServeMux) {
		if err := http.Serve(lis, mux); err != nil {
			log.Warn(err.Error())
		}
	}(s.gatewayListener, s.mux)

	return nil
}

func (s *Server) startIpc() error {
	// Ensure the IPC path exists and remove any previous leftover
	if err := os.MkdirAll(filepath.Dir(s.config.IpcAddress()), 0751); err != nil {
		return err
	}
	os.Remove(s.config.IpcAddress())
	if s.config.IpcAddress() != "" {
		s.ipcHandler = grpc.NewServer(s.serverOpts...)
		c, err := net.Listen("unix", s.config.IpcAddress())
		if err != nil {
			return err
		}
		s.ipcListener = c
		os.Chmod(s.config.IpcAddress(), 0600)

		go func(handler *grpc.Server, lis net.Listener) {
			if err := handler.Serve(lis); err != nil {
				log.Error(err.Error())
			}
		}(s.ipcHandler, s.ipcListener)
	}

	return nil
}

// Stop stops the underlying grpc.Server and close the listener
func (s *Server) Stop() {
	s.stopGrpc()
	s.stopIpc()
}

func (s *Server) stopGrpc() {
	if s.handler != nil {
		s.handler.Stop()
		s.handler = nil
	}

	if s.gatewayListener != nil {
		_ = s.gatewayListener.Close()
		s.gatewayListener = nil
	}
}

func (s *Server) stopIpc() {
	if s.ipcHandler != nil {
		s.ipcHandler.Stop()
		s.ipcHandler = nil
	}

	if s.ipcListener != nil {
		if err := s.ipcListener.Close(); err != nil {
			log.Error(err.Error())
		}
		s.ipcListener = nil
	}
}

// Register registers all the given GApis
func (s *Server) Register(ctx context.Context, gapis []GApi) {
	// Generate the whitelist based on the allowed modules
	whitelist := make(map[string]bool)
	for _, module := range s.config.Modules {
		whitelist[module] = true
	}
	// register grpc server
	for _, stub := range gapis {
		if whitelist[stub.Namespace()] || (len(whitelist) == 0 && stub.IsPublic()) {
			s.register(ctx, stub)
			log.Debug("GRpc registered", "namespace", stub.Namespace())
		}
	}
}

func (s *Server) register(ctx context.Context, stub GApi) {
	if s.handler != nil {
		stub.RegisterServer(s.handler)
		stub.RegisterJsonRpc(ctx, s.mux, s.config.Address(), s.dialOpts)
	}
	if s.ipcHandler != nil {
		stub.RegisterServer(s.ipcHandler)
		stub.RegisterJsonRpc(ctx, s.mux, s.config.IpcAddress(), s.dialOpts)
	}
}
