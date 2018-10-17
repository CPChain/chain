package main

import (
	"bitbucket.org/cpchain/chain/apis"
	"bitbucket.org/cpchain/chain/apis/server/chain"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/crypto"
	"bitbucket.org/cpchain/chain/eth"
	"bitbucket.org/cpchain/chain/node"
	"github.com/ethereum/go-ethereum/common"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	context "golang.org/x/net/context"
	"google.golang.org/grpc"
)

const (
	rpcEndpoint  = ":50051"
	httpEndpoint = ":50052"
	testAddress  = "0x8605cdbbdb6d264aa742e77020dcbc58fcdce182"
)

var (
	ethConf = &eth.Config{
		Genesis:   core.DeveloperGenesisBlock(15, common.Address{}),
		Etherbase: common.HexToAddress(testAddress),
	}
	testNodeKey, _ = crypto.GenerateKey()
)

type MyNode struct {
	node      *node.Node
	rpcServer *apis.ApiServer
	rpsSvrs   []apis.Api
}

func newNode(ethNode *node.Node) *MyNode {
	return &MyNode{
		node:      ethNode,
		rpcServer: NewTestApiServer(),
		rpsSvrs:   make([]apis.Api, 0, 0),
	}
}

func NewTestApiServer() *apis.ApiServer {
	ctx := context.Background()
	ctx, cancel := context.WithCancel(ctx)
	return apis.NewApiServer(ctx, cancel, runtime.NewServeMux(), rpcEndpoint, httpEndpoint, []grpc.DialOption{grpc.WithInsecure()})
}

// TODO: @sangh add test file
func newEthereumNode() *node.Node {
	node.DefaultConfig.P2P.PrivateKey = testNodeKey
	stack, err := node.New(&node.DefaultConfig)
	if err != nil {
		log.Fatalf("Failed to create network node: %v", err)
	}

	// if err = stack.Register(func(ctx *node.ServiceContext) (node.Service, error) { return eth.New(ctx, ethConf) }); err != nil {
	// 	log.Fatalf("failed to register Ethereum protocol: %v", err)
	// }

	return stack
}

func (my *MyNode) Run() {
	if err := my.node.Start(); err != nil {
		log.Fatalln(err.Error())
	}

	if err := my.rpcServer.Run(); err != nil {
		log.Fatalln(err.Error())
	}
}

func (my *MyNode) Register(api apis.Api) {
	my.rpsSvrs = append(my.rpsSvrs, api)
	my.rpcServer.Register(api)
}

func main() {
	myNode := newNode(newEthereumNode())

	// var ethereum eth.Ethereum
	// if err := myNode.node.Service(&ethereum); err != nil {
	// 	log.Fatalf("Ethereum service not running: %v", err)
	// }

	// myNode.Register(api_chain_stub.NewPublicEthereumServer(&ethereum))
	myNode.Register(api_chain_stub.NewPublicEthereumServer(nil))

	myNode.Run()

	log.Info("Over")
}
