package api

import (
	"context"
	"net"
	"net/http"
	"os"
	"path/filepath"

	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"google.golang.org/grpc"
)

type Server struct {
	config *Config

	handler  *grpc.Server
	listener net.Listener

	ipcHandler  *grpc.Server
	ipcListener net.Listener
	// TODO: @sangh inpro

	mux        *runtime.ServeMux
	dialOpts   []grpc.DialOption
	serverOpts []grpc.ServerOption
}

func NewSerever(cfg Config) *Server {
	// TODO: @sangh use config to set
	serverOpts := []grpc.ServerOption{}

	s := &Server{
		config:  &cfg,
		handler: grpc.NewServer(serverOpts...),
		mux:     runtime.NewServeMux(),
	}

	if cfg.IpcAddress() != "" {
		s.ipcHandler = grpc.NewServer(serverOpts...)
	}

	return s
}

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
	c, err := net.Listen("tcp", s.config.Address())
	if err != nil {
		return nil
	}
	s.listener = c
	go func() {
		if err := s.handler.Serve(s.listener); err != nil {
			log.Error(err.Error())
		}
	}()

	go func() {
		if err := http.ListenAndServe(s.config.GatewayAddress(), s.mux); err != nil {
			log.Error(err.Error())
		}
	}()
	return nil
}

func (s *Server) startIpc() error {
	// Ensure the IPC path exists and remove any previous leftover
	if err := os.MkdirAll(filepath.Dir(s.config.IpcAddress()), 0751); err != nil {
		return err
	}
	os.Remove(s.config.IpcAddress())
	if s.config.IpcAddress() != "" {
		c, err := net.Listen("unix", s.config.IpcAddress())
		if err != nil {
			return err
		}
		s.ipcListener = c

		go func() {
			if err := s.ipcHandler.Serve(s.ipcListener); err != nil {
				log.Error(err.Error())
			}
		}()
		os.Chmod(s.config.IpcAddress(), 0600)
	}

	return nil
}

func (s *Server) Stop() {
	s.stopGrpc()
	s.stopIpc()
}

func (s *Server) stopIpc() {
	if s.ipcHandler != nil {
		s.ipcHandler.GracefulStop()
	}

	if s.ipcListener != nil {
		s.ipcListener.Close()
	}
}

func (s *Server) stopGrpc() {
	if s.handler != nil {
		s.handler.GracefulStop()
	}
	if s.listener != nil {
		s.listener.Close()
	}
}

func (s *Server) Register(gapis []API) {
	ctx := context.Background()
	// register grpc server
	for _, stub := range gapis {
		s.register(ctx, stub)
	}
}

func (s *Server) register(ctx context.Context, stub API) {
	if s.handler != nil {
		stub.RegisterServer(s.handler)
		stub.RegisterGateway(ctx, s.mux, s.config.Address(), s.dialOpts)
	}
	if s.ipcHandler != nil {
		stub.RegisterServer(s.ipcHandler)
		stub.RegisterGateway(ctx, s.mux, s.config.IpcAddress(), s.dialOpts)
	}
}
