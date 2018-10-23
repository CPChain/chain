package apis

import (
	"crypto/tls"
	"crypto/x509"
	"errors"
	"fmt"
	"io/ioutil"
	"net"

	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials"
)

var (
	crt = "server.crt"
	key = "server.key"
	// ca  = "ca.crt"
)

type Server struct {
	server   *grpc.Server
	listener net.Listener
	endpoint string

	// Key           []byte
	// Crt           []byte
	certPool      *x509.CertPool
	certificate   tls.Certificate
	clientRootCAs map[string]*x509.Certificate

	useTLS           bool
	RequireandVerify bool
}

func NewServer(endpoint string) (*Server, error) {
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
		endpoint:    endpoint,
	}, nil
}

func (s *Server) Start() error {
	listener, err := net.Listen("tcp", s.endpoint)
	if err != nil {
		return err
	}

	// Create the TLS credentials
	creds := credentials.NewTLS(&tls.Config{
		ClientAuth:   tls.RequireAndVerifyClientCert,
		Certificates: []tls.Certificate{s.certificate},
		ClientCAs:    s.certPool,
	})

	s.listener = listener
	s.server = grpc.NewServer(grpc.Creds(creds))

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
