package gapis

import (
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

// API every grpc instance service
type API interface {
	// RegisterServer register api instance to grpc
	RegisterServer(server *grpc.Server)
	// RegisterProxy register api instance to grpc gateway
	RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption)
	// Namespace service name
	Namespace() string
	// IsPublic return true if public to user
	IsPublic() bool
}

// Service one type service
// degradation for node.Service
// type Service interface {
// 	// APIs all api instance provided by service
// 	APIs() []API
// }
