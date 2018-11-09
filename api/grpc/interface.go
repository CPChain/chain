package grpc

import (
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

// GApi Named Register is better
type GApi interface {
	IsPublic() bool
	Namespace() string
	RegisterServer(*grpc.Server)
	RegisterJsonRpc(context.Context, *runtime.ServeMux, string, []grpc.DialOption)
}
