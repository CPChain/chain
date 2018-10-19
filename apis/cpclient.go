package apis

import "google.golang.org/grpc"

type CpcClient struct {
	*grpc.ClientConn
}
