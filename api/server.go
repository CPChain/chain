package api

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

// Server Grpc Server
type Server struct {
	config *Config

	handler  *grpc.Server
	listener net.Listener

	ipcHandler  *grpc.Server
	ipcListener net.Listener
	cancel      context.CancelFunc

	mux        *runtime.ServeMux
	dialOpts   []grpc.DialOption
	serverOpts []grpc.ServerOption
}

// NewServer creates a new implementation of a Server
func NewSerever(dataDir string, module []string, cfg Config) *Server {
	// update grpc config
	cfg.DataDir = dataDir
	cfg.Modules = make([]string, len(module))
	copy(cfg.Modules, module)

	// set default options here, TODO: @sangh add tls support
	serverOpts := []grpc.ServerOption{}
	dialOpts := []grpc.DialOption{grpc.WithInsecure()}

	s := &Server{
		config:     &cfg,
		handler:    grpc.NewServer(serverOpts...),
		mux:        runtime.NewServeMux(),
		serverOpts: serverOpts,
		dialOpts:   dialOpts,
	}

	if cfg.IpcAddress() != "" {
		s.ipcHandler = grpc.NewServer(serverOpts...)
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
		os.Chmod(s.config.IpcAddress(), 0600)

		go func() {
			if err := s.ipcHandler.Serve(s.ipcListener); err != nil {
				log.Error(err.Error())
			}
		}()
	}

	return nil
}

// Stop stops the underlying grpc.Server and close the listener
func (s *Server) Stop() {
	s.stopGrpc()
	s.stopIpc()
}

func (s *Server) stopIpc() {
	if s.ipcHandler != nil {
		s.ipcHandler.Stop()
		s.ipcHandler = nil
	}

	if s.ipcListener != nil {
		s.ipcListener.Close()
		s.ipcListener = nil
	}
}

func (s *Server) stopGrpc() {
	if s.cancel != nil {
		s.cancel()
	}
	if s.handler != nil {
		s.handler.Stop()
		s.handler = nil
	}
	if s.listener != nil {
		s.listener.Close()
		s.listener = nil
	}
}

// Register regists all the given apis
func (s *Server) Register(ctx context.Context, cancel func(), gapis []Api) {
	s.cancel = cancel
	// Generate the whitelist based on the allowed modules
	whitelist := make(map[string]bool)
	for _, module := range s.config.Modules {
		whitelist[module] = true
	}
	// register grpc server
	for _, stub := range gapis {
		if whitelist[stub.Namespace()] || (len(whitelist) == 0 && stub.IsPublic()) {
			s.register(ctx, stub)
			log.Error("Grpc registered", "namespace", stub.Namespace())
		}
	}
}

func (s *Server) register(ctx context.Context, stub Api) {
	if s.handler != nil {
		stub.RegisterServer(s.handler)
		stub.RegisterGateway(ctx, s.mux, s.config.Address(), s.dialOpts)
	}
	if s.ipcHandler != nil {
		stub.RegisterServer(s.ipcHandler)
		stub.RegisterGateway(ctx, s.mux, s.config.IpcAddress(), s.dialOpts)
	}
}
