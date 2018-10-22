package apis

import (
	"net"
	"time"

	"google.golang.org/grpc"
)

func withDialer() grpc.DialOption {
	return grpc.WithDialer(func(addr string, timeout time.Duration) (net.Conn, error) {
		_, wc := net.Pipe()
		return wc, nil
	})
}

func DialInProc(handler *grpc.Server) (*grpc.ClientConn, error) {
	return grpc.Dial("", grpc.WithInsecure(), withDialer())
}
