package apis

import (
	"net"
	"net/http"

	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

type Api interface {
	RegisterServer(server *grpc.Server)
	RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption)
}

type ApiServer struct {
	Context      context.Context
	RpcEndpoint  string
	HttpEndpoint string
	Mux          *runtime.ServeMux
	DialOption   []grpc.DialOption
	Server       *grpc.Server
	Cancel       context.CancelFunc
}

// TODO: @sangh after start, if can register new service

func NewApiServer(ctx context.Context, cancel context.CancelFunc, mux *runtime.ServeMux, rpcEndpoint, httpEndpoint string, opts []grpc.DialOption) *ApiServer {
	return &ApiServer{
		Context:      ctx,
		Cancel:       cancel,
		RpcEndpoint:  rpcEndpoint,
		HttpEndpoint: httpEndpoint,
		Mux:          mux,
		DialOption:   opts,
		Server:       grpc.NewServer(),
	}
}

// curl -X POST "http://localhost:8080/v1/apis/public/coinbase"
func (server *ApiServer) Register(api Api) {
	api.RegisterServer(server.Server)
	api.RegisterProxy(server.Context, server.Mux, server.RpcEndpoint, server.DialOption)
}

func (server *ApiServer) Run() error {
	listen, err := net.Listen("tcp", server.RpcEndpoint)
	if err != nil {
		return err
	}

	go server.Server.Serve(listen)
	http.ListenAndServe(server.HttpEndpoint, server.Mux)

	return nil
}

func (server *ApiServer) Stop() {
	server.Cancel()
}
