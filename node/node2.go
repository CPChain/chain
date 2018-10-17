package node

import (
	"context"
	"net"
	"net/http"
	"reflect"
	"runtime"

	"bitbucket.org/cpchain/chain/apis"
	"github.com/ethereum/go-ethereum/log"
	"google.golang.org/grpc"
)

type MyNode struct {
	context      context.Context
	cancel       context.CancelFunc
	rpcEndpoint  string
	httpEndpoint string

	services     map[reflect.Type]apis.Service
	rpcListener net.Listener

	mux        *runtime.ServeMux
	dialOption []grpc.DialOption
	server     *grpc.Server
}

func NewMyNode() *MyNode {
	ctx := context.Background()
	ctx, cancel := context.WithCancel(ctx)
	return &MyNode{
		context:      ctx,
		cancel:       cancel,
		rpcEndpoint:  cfg.RpcEndpoint(),
		httpEndpoint: cfg.HttpEndpoint(),

		mux:        runtime.NewServeMux(),
		dialOption: []grpc.DialOption{grpc.WithInsecure()},
		server:     grpc.NewServer(),
	}
}

func (n *MyNode) Register(service apis.Service) {
	for _, svr := range n.services {
		svr := svr.APIs()
		for _, s := range svr {
			s.Register(n.server, n.context, n.mux, n.rpcEndpoint, n.httpEndpoint, n.dialOption)
		}
	}
}

func (n *MyNode) Start() {
	n.rpcListener, err := net.Listen("tcp", ":50051")
	if err != nil {
		log.Fatal("service start failed: ", err.Error())
	}

	// start server listening
	go n.server.Serve(n.rpcListener)
	// start proxy server listeningk
	go http.ListenAndServe(n.httpEndpoint, n.mux)
}

func (n *MyNode) Stop() {
	n.context.cancel()
}

func (n *MyNode) Wait() {
	// TODO: @sangh
}

func (n *MyNode) Restart() error {
	if err := n.Stop(); err != nil {
		return err
	}
	if err := n.Start(); err != nil {
		return err
	}
	return nil
}
