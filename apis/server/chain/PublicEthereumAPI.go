package api_chain_stub

import (
	"bitbucket.org/cpchain/chain/apis/pb/chain"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/eth"
	"github.com/golang/protobuf/ptypes/empty"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

type PublicEthereumServer struct {
	e *eth.Ethereum
}

func NewPublicEthereumServer(ethereum *eth.Ethereum) *PublicEthereumServer {
	return &PublicEthereumServer{e: ethereum}
}

func (api *PublicEthereumServer) Etherbase(ctx context.Context, args *empty.Empty) (*api_chain_pb.Address, error) {
	address, err := api.e.Etherbase()
	if err != nil {
		return nil, err
	}
	return &api_chain_pb.Address{Address: address.Bytes()}, nil
}

func (api *PublicEthereumServer) Coinbase(ctx context.Context, args *empty.Empty) (*api_chain_pb.Address, error) {
	// return api.Etherbase(ctx, args)
	return &api_chain_pb.Address{Address: []byte("0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6")}, nil
}

func (api *PublicEthereumServer) Hashrate(ctx context.Context, args *empty.Empty) (*api_chain_pb.Rate, error) {
	return &api_chain_pb.Rate{Rate: api.e.Miner().HashRate()}, nil
}

func (api *PublicEthereumServer) RegisterServer(server *grpc.Server) {
	api_chain_pb.RegisterPublicEthereumAPIServiceServer(server, api)
}

func (api *PublicEthereumServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	err := api_chain_pb.RegisterPublicEthereumAPIServiceHandlerFromEndpoint(ctx, mux, endpoint, opts)
	if err != nil {
		log.Fatal(err.Error())
	}
}
