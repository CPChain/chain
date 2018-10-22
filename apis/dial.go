package apis

import (
	"google.golang.org/grpc"
)

func DefaultDialFactory() grpc.DialOption {
	// dialOpts := []grpc.DialOption{grpc.WithBlock()}
	// dialOpts = append(dialOpts, grpc.WithDefaultCallOptions(grpc.MaxCallRecvMsgSize(comm.MaxRecvMsgSize), grpc.MaxCallSendMsgSize(comm.MaxSendMsgSize)))

	// ctx, cancel := context.WithTimeout(context.Background(), getConnectionTimeout())
	// defer cancel()
	// return grpc.DialContext(ctx, endpoint, dialOpts...)
	return nil
}
