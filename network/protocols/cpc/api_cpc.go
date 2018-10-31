package cpc

import (
	"fmt"

	"bitbucket.org/cpchain/chain/api/v1/common"
	"bitbucket.org/cpchain/chain/api/v1/cpc"
	"bitbucket.org/cpchain/chain/node/miner"
	"github.com/golang/protobuf/ptypes/empty"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

// Coinbase provides an API to access Ethereum full node-related
// information.
type Coinbase struct {
	c *CpchainService
}

// NewCoinbase creates a new Ethereum protocol API for full nodes.
func NewCoinbase(c *CpchainService) *Coinbase {
	return &Coinbase{c}
}

// IsPublic if public default
func (c *Coinbase) IsPublic() bool {
	return true
}

// Namespace namespace naem
func (c *Coinbase) Namespace() string {
	return "cpc"
}

// RegisterServer register api to grpc
func (c *Coinbase) RegisterServer(s *grpc.Server) {
	cpc.RegisterCoinbaseServer(s, c)
}

// RegisterJsonRpcHttp register api to restfull json
func (c *Coinbase) RegisterGateway(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	cpc.RegisterCoinbaseHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// Coinbase is the address that mining rewards will be send to
func (c *Coinbase) Coinbase(ctx context.Context, req *empty.Empty) (*common.Address, error) {
	addr, err := c.c.Etherbase()
	return &common.Address{Address: addr.String()}, err
}

// MinerReader provides an API to control the miner.
// It offers only methods that operate on data that pose no security risk when it is publicly accessible.
type MinerReader struct {
	e     *CpchainService
	agent *miner.RemoteAgent
}

// NewMinerReader create a new MinerReader instance.
func NewMinerReader(c *CpchainService) *MinerReader {
	agent := miner.NewRemoteAgent(c.BlockChain(), c.Engine())
	c.Miner().Register(agent)

	return &MinerReader{c, agent}
}

// Mining returns an indication if this node is currently mining.
func (m *MinerReader) Mining(ctx context.Context, req *empty.Empty) (*common.IsOk, error) {
	return &common.IsOk{IsOk: m.e.IsMining()}, nil
}

// GetWork returns a work package for external miner. The work package consists of 3 strings
// result[0], 32 bytes hex encoded current block header pow-hash
// result[1], 32 bytes hex encoded seed hash used for DAG
// result[2], 32 bytes hex encoded boundary condition ("target"), 2^256/difficulty
func (m *MinerReader) GetWork(ctx context.Context, req *empty.Empty) (*cpc.Works, error) {
	if !m.e.IsMining() {
		// TODO: @liuq fix this.
		if err := m.e.StartMining(false, nil); err != nil {
			return &cpc.Works{}, err
		}
	}
	work, err := m.agent.GetWork()
	if err != nil {
		return &cpc.Works{}, fmt.Errorf("mining not ready: %v", err)
	}
	mwork := make(map[int32]string)
	for i, w := range work {
		mwork[int32(i)] = w
	}
	return &cpc.Works{Works: mwork}, nil
}
