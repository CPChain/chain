package cpc

import (
	"bitbucket.org/cpchain/chain/api/v1"
	"fmt"
	"github.com/golang/protobuf/ptypes/empty"
	"golang.org/x/net/context"

	"bitbucket.org/cpchain/chain/node/miner"
)

// Coinbase provides an API to access Ethereum full node-related
// information.
type Coinbase struct {
	e *CpchainService
}

// NewCoinbase creates a new Ethereum protocol API for full nodes.
func NewCoinbase(e *CpchainService) *Coinbase {
	return &Coinbase{e}
}

// Coinbase is the address that mining rewards will be send to (alias for Etherbase)
func (api *Coinbase) Coinbase(ctx context.Context, req *empty.Empty) (*protos.Address, error) {
	addr, err := api.e.Etherbase()
	return &protos.Address{Address:addr.String()}, err
}

// MinerReader provides an API to control the miner.
// It offers only methods that operate on data that pose no security risk when it is publicly accessible.
type MinerReader struct {
	e     *CpchainService
	agent *miner.RemoteAgent
}

// NewMinerReader create a new MinerReader instance.
func NewMinerReader(e *CpchainService) *MinerReader {
	agent := miner.NewRemoteAgent(e.BlockChain(), e.Engine())
	e.Miner().Register(agent)

	return &MinerReader{e, agent}
}

// Mining returns an indication if this node is currently mining.
func (api *MinerReader) Mining(ctx context.Context, req *empty.Empty) (*protos.IsOk, error){
	return &protos.IsOk{IsOk:api.e.IsMining()}, nil
}

// GetWork returns a work package for external miner. The work package consists of 3 strings
// result[0], 32 bytes hex encoded current block header pow-hash
// result[1], 32 bytes hex encoded seed hash used for DAG
// result[2], 32 bytes hex encoded boundary condition ("target"), 2^256/difficulty
func (api *MinerReader) GetWork(ctx context.Context, req *empty.Empty) (*protos.Works, error) {
	if !api.e.IsMining() {
		// TODO: @liuq fix this.
		if err := api.e.StartMining(false, nil); err != nil {
			return &protos.Works{}, err
		}
	}
	work, err := api.agent.GetWork()
	if err != nil {
		return &protos.Works{}, fmt.Errorf("mining not ready: %v", err)
	}
	mwork := make(map[uint32]string)
	for i, w := range work {
	    mwork[i] = w
	}
	return &protos.Works{Works:mwork}, nil
}

