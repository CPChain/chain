package gapis

import (
	"crypto/tls"
	"crypto/x509"
	"errors"
	"fmt"
	"io/ioutil"
	"net"

	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials"
)

var (
	crt = "server.crt"
	key = "server.key"
	// ca  = "ca.crt"
)

type Server struct {
	config *ServerConfig

	server   *grpc.Server
	listener net.Listener

	certPool      *x509.CertPool
	certificate   tls.Certificate
	clientRootCAs map[string]*x509.Certificate

	dialOpts   []grpc.DialOption
	serverOpts []grpc.ServerOption
}

func NewServer(cfg *ServerConfig) (*Server, error) {
	certPool, err := createCertPool()
	if err != nil {
		return nil, err
	}

	// Load the certificates from disk
	certificate, err := tls.LoadX509KeyPair(crt, key)
	if err != nil {
		return nil, fmt.Errorf("could not load server key pair: %s", err.Error())
	}

	ca, err := ioutil.ReadFile(ca)
	if err != nil {
		return nil, fmt.Errorf("could not read ca certificate: %s", err)
	}

	if ok := certPool.AppendCertsFromPEM(ca); !ok {
		return nil, errors.New("failed to append ca certs")
	}

	return &Server{
		certPool:    certPool,
		certificate: certificate,
		config:      cfg,
		dialOpts:    []grpc.DialOption{grpc.WithInsecure()},
		serverOpts:  []grpc.ServerOption{},
	}, nil
}

func (s *Server) Serve(listener net.Listener) error {
	s.listener = listener
	if s.config.useTLS {
		// Create the TLS credentials
		creds := credentials.NewTLS(&tls.Config{
			ClientAuth:   tls.RequireAndVerifyClientCert,
			Certificates: []tls.Certificate{s.certificate},
			ClientCAs:    s.certPool,
		})

		// Create the TLS credentials
		dialCreds := credentials.NewTLS(&tls.Config{
			ServerName:   s.config.endpoint,
			Certificates: []tls.Certificate{s.certificate},
			RootCAs:      s.certPool,
		})

		s.dialOpts = append(s.dialOpts, grpc.WithTransportCredentials(dialCreds))
		s.serverOpts = append(s.serverOpts, grpc.Creds(creds))

	}

	s.server = grpc.NewServer(s.serverOpts...)

	// serve and listen
	if err := s.server.Serve(listener); err != nil {
		return fmt.Errorf("grpc serve error: %s", err)
	}
	return nil
}

func (s *Server) Stop() {
	if s.server != nil {
		s.server.GracefulStop()
	}
	if s.listener != nil {
		s.listener.Close()
	}
}

func (s *Server) RegisterApi(api API) {
	api.RegisterServer(s.server)
	api.RegisterProxy(context.Background(), runtime.NewServeMux(), s.config.endpoint, s.dialOpts)
}

// Create a certificate pool from the certificate authority
func createCertPool() (*x509.CertPool, error) {
	certPool := x509.NewCertPool()
	ca, err := ioutil.ReadFile(ca)
	if err != nil {
		return nil, err
	}

	if ok := certPool.AppendCertsFromPEM(ca); !ok {
		return nil, errors.New("failed to append client certs")
	}

	return certPool, nil
}
