package api

import (
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

// Named Register is better
type Api interface {
	IsPublic() bool
	Namespace() string
	RegisterServer(*grpc.Server)
	RegisterGateway(context.Context, *runtime.ServeMux, string, []grpc.DialOption)
}
