package main

import (
	"bitbucket.org/cpchain/chain/apis/pb/chain"
	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/golang/protobuf/ptypes/empty"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

func main() {
	// Set up a connection to the server.
	conn, err := grpc.Dial("localhost:50051", grpc.WithInsecure())
	if err != nil {
		log.Fatalf("did not connect: %v", err)
	}
	defer conn.Close()
	c := api_chain_pb.NewPublicEthereumAPIServiceClient(conn)

	addressBytes, err := c.Coinbase(context.Background(), &empty.Empty{})
	if err != nil {
		log.Fatalf("could not greet: %v", err)
	}
	log.Printf("Greeting: %s", string(addressBytes.Address))
}
