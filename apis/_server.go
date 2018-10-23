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
	ca  = "ca.crt"
)

type Server struct {
	server   *grpc.Server
	listener net.Listener
	path     string
	port     uint

	// Key           []byte
	// Crt           []byte
	certPool *x509.CertPool
	certificate *tls.Certificate
	clientRootCAs map[string]*x509.Certificate

	useTLS           bool
	RequireandVerify bool
}

func New() (*Server, error) {
	certPool, err := createCertPool()
	if err != nil {
		return nil, err
	}

	// Load the certificates from disk
	certificate, err := tls.LoadX509KeyPair(crt, key)
	if err != nil {
		return nil, fmt.Errorf("could not load server key pair: %s", err.Error())
	}

	if ok := certPool.AppendCertsFromPEM(ca); !ok {
		return nil, errors.New("failed to append ca certs")
	}

	return &Server{
		certPool: certPool,
		certificate: certificate,
	}
}

func (s *Server) Start() error {
	lis, err := net.Listen("tcp", address)
	if err != nil {
		return err
	}

	// Create the TLS credentials
	creds := credentials.NewTLS(&tls.Config{
		ClientAuth:   tls.RequireAndVerifyClientCert,
		Certificates: []tls.Certificate{certificate},
		ClientCAs:    certPool,
	})

	s.listener = listener
	s.server := grpc.NewServer(grpc.Creds(creds))

	// serve and listen
	if err := svr.Serve(lis); err != nil {
		return fmt.Errorf("grpc serve error: %s", err)
	}
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
