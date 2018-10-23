package gapis

import (
	"crypto/tls"
	"crypto/x509"
	"errors"
	"fmt"
	"io/ioutil"
	"net"
	"net/http"
	"os"
	"path/filepath"

	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials"
)

var (
	crt = "server.crt"
	key = "server.key"
)

type Server struct {
	endpoint string

	server   *grpc.Server
	listener net.Listener
	mux      *runtime.ServeMux

	certPool      *x509.CertPool
	certificate   tls.Certificate
	clientRootCAs map[string]*x509.Certificate

	dialOpts   []grpc.DialOption
	serverOpts []grpc.ServerOption
}

func dirNotExitCreate(datadir, file string) (bool, error) {
	_, err := os.Stat(datadir)
	if err == nil {
		_, err = os.Stat(filepath.Join(datadir, file))
		if err == nil {
			return true, nil
		}
	}

	return false, err
}

func NewServer(endpoint string, datadir string, useTls bool) (*Server, error) {
	s := &Server{
		endpoint:   endpoint,
		dialOpts:   []grpc.DialOption{grpc.WithInsecure()},
		serverOpts: []grpc.ServerOption{},
		mux:        runtime.NewServeMux(),
	}

	var err error
	if useTls {
		s.certPool, err = createCertPool()
		if err != nil {
			return nil, err
		}

		// Load the certificates from disk
		s.certificate, err = tls.LoadX509KeyPair(crt, key)
		if err != nil {
			return nil, fmt.Errorf("could not load server key pair: %s", err.Error())
		}

		ca, err := ioutil.ReadFile(filepath.Join(datadir, ca))
		if err != nil {
			return nil, fmt.Errorf("could not read ca certificate: %s", err)
		}

		if ok := s.certPool.AppendCertsFromPEM(ca); !ok {
			return nil, errors.New("failed to append ca certs")
		}

		// Create the TLS credentials
		creds := credentials.NewTLS(&tls.Config{
			ClientAuth:   tls.RequireAndVerifyClientCert,
			Certificates: []tls.Certificate{s.certificate},
			ClientCAs:    s.certPool,
		})

		// Create the TLS credentials
		dialCreds := credentials.NewTLS(&tls.Config{
			ServerName:   endpoint,
			Certificates: []tls.Certificate{s.certificate},
			RootCAs:      s.certPool,
		})

		s.dialOpts = append(s.dialOpts, grpc.WithTransportCredentials(dialCreds))
		s.serverOpts = append(s.serverOpts, grpc.Creds(creds))

	}

	s.server = grpc.NewServer(s.serverOpts...)
	return s, nil
}

func (s *Server) Serve(proxyEndpoint string, listener net.Listener) error {
	s.listener = listener
	// serve and listen
	go func() {
		if err := s.server.Serve(listener); err != nil {
			log.Error(err.Error())
		}
	}()

	go func() {
		if err := http.ListenAndServe(proxyEndpoint, s.mux); err != nil {
			log.Error(err.Error())
		}
	}()

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
	api.RegisterProxy(context.Background(), s.mux, s.endpoint, s.dialOpts)
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
