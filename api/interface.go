package api

import (
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

// Named Register is better
type GApi interface {
	IsPublic() bool
	Namespace() string
	RegisterServer(*grpc.Server)
	RegisterJsonRpcHttp(context.Context, *runtime.ServeMux, string, []grpc.DialOption)
}
