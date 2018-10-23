package apis

import (
	"crypto/tls"
	"crypto/x509"
	"net"
	"sync"
	"sync/atomic"

	"bitbucket.org/cpchain/chain/commons/log"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials"
)

type GRPCServer struct {
	address           string
	listener          net.Listener
	server            *grpc.Server
	serverCertificate atomic.Value
	serverKeyPem      []byte
	lock              *sync.Mutex
}

var (
	KeyPair  *tls.Certificate
	CertPool *x509.CertPool
)

func NewGRPCServer(endpoint string) *GRPCServer {
	listener, err := net.Listen("tcp", endpoint)
	if err != nil {
		log.FatalLevel(err.Error())
	}

	grpcServer := &GRPCServer{
		address:  listener.Addr().String(),
		listener: listener,
	}

	serverOptions := []grpc.ServerOption{
		grpc.Creds(credentials.NewClientTLSFromCert(CertPool, endpoint))
	}
}

func init() {
	var err error
	pair, err := tls.X509KeyPair([]byte(insecure.Cert), []byte(insecure.Key))
	if err != nil {
		panic(err)
	}
	KeyPair = &pair
	CertPool = x509.NewCertPool()
	ok := CertPool.AppendCertsFromPEM([]byte(insecure.Cert))
	if !ok {
		panic("bad certs")
	}
}

func NewServer(endpoint string) *grpc.Server {
	opts := []grpc.ServerOption{
		grpc.Creds(credentials.NewClientTLSFromCert(CertPool, endpoint))
	}

	grpcServer := grpc.NewServer(opts...)
	pb.RegisterEchoServiceServer(grpcServer, newServer())
	ctx := context.Background()

	dcreds := credentials.NewClientTLSFromCert(CertPool, endpoint)

	// dopts := []grpc.DialOption{grpc.WithTransportCredentials(dcreds)}
	// register need

	err = srv.Serve(tls.NewListener(conn, srv.TLSConfig))

	if err != nil {
		log.Fatal("ListenAndServe: ", err)
	}
}
