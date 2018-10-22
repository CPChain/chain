package apis

// type GRPCServer struct {
// 	address           string
// 	Listener          net.Listener
// 	ConnectionTimeout uint64
// 	Certificate
// 	UseTLS bool
// }

// var (
// 	KeyPair  *tls.Certificate
// 	CertPool *x509.CertPool
// )

// func init() {
// 	var err error
// 	pair, err := tls.X509KeyPair([]byte(insecure.Cert), []byte(insecure.Key))
// 	if err != nil {
// 		panic(err)
// 	}
// 	KeyPair = &pair
// 	CertPool = x509.NewCertPool()
// 	ok := CertPool.AppendCertsFromPEM([]byte(insecure.Cert))
// 	if !ok {
// 		panic("bad certs")
// 	}
// }

// func NewServer(endpoint string) *grpc.Server {
// 	opts := []grpc.ServerOption{
// 		grpc.Creds(credentials.NewClientTLSFromCert(CertPool, endpoint))}

// 	grpcServer := grpc.NewServer(opts...)
// 	pb.RegisterEchoServiceServer(grpcServer, newServer())
// 	ctx := context.Background()

// 	dcreds := credentials.NewClientTLSFromCert(CertPool, endpoint)

// 	// dopts := []grpc.DialOption{grpc.WithTransportCredentials(dcreds)}
// 	// register need

// 	err = srv.Serve(tls.NewListener(conn, srv.TLSConfig))

// 	if err != nil {
// 		log.Fatal("ListenAndServe: ", err)
// 	}
// }
