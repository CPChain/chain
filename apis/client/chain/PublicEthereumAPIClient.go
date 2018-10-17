package main

import (
	"reflect"

	"bitbucket.org/cpchain/chain/apis/pb/chain"
	"bitbucket.org/cpchain/chain/commons/log"
	"google.golang.org/grpc"
)

func main() {
	conn, err := grpc.Dial("", grpc.WithInsecure())
	if err != nil {
		log.Fatalf("did not connect: %v", err)
	}
	defer conn.Close()
	svr := apis_chain.NewPublicEthereumAPIClient(conn)

	addressBytes, err := svr.Coinbase(&apis_chain.Empty{})
	if err != nil {
		log.Error(err.Error())
	}

	expected := ""

	if reflect.DeepEqual(x, y) {
	}
}
