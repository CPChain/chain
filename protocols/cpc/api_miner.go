// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package cpc

import (
	"math/big"

	pb "bitbucket.org/cpchain/chain/api/grpc/v1/common"
	"bitbucket.org/cpchain/chain/api/grpc/v1/miner"
	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/ethereum/go-ethereum/common"
	"github.com/golang/protobuf/ptypes/empty"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

// MinerManager provides private RPC methods to control the miner.
// These methods can be abused by external users and must be considered insecure for use by untrusted users.
type MinerManager struct {
	c *CpchainService
}

// NewMinerManager create a new RPC service which controls the miner of this node.
func NewMinerManager(c *CpchainService) *MinerManager {
	return &MinerManager{c: c}
}

// IsPublic if public default
func (m *MinerManager) IsPublic() bool {
	return false
}

// Namespace namespace
func (m *MinerManager) Namespace() string {
	return "miner"
}

// RegisterServer register api to grpc
func (m *MinerManager) RegisterServer(s *grpc.Server) {
	miner.RegisterMinerManagerServer(s, m)
}

// RegisterJsonRpc register api to restfull json
func (m *MinerManager) RegisterJsonRpc(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	miner.RegisterMinerManagerHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// Start the miner with the given number of threads. If threads is nil the number
// of workers started is equal to the number of logical CPUs that are usable by
// this process. If mining is already running, this method adjust the number of
// threads allowed to use.
func (api *MinerManager) Start(ctx context.Context, threads *miner.Threads) (*empty.Empty, error) {
	// Set the number of threads if the seal engine supports it
	if threads == nil {
		threads = new(miner.Threads)
	} else if threads.Threads == 0 {
		threads.Threads = -1 // Disable the miner from within
	}
	type threaded interface {
		SetThreads(threads int)
	}
	if th, ok := api.c.engine.(threaded); ok {
		log.Info("Updated mining threads", "threads", *threads)
		th.SetThreads(int(threads.Threads))
	}
	// Start the miner and return
	if !api.c.IsMining() {
		// Propagate the initial price point to the transaction pool
		api.c.lock.RLock()
		price := api.c.gasPrice
		api.c.lock.RUnlock()

		api.c.txPool.SetGasPrice(price)
		// TODO: @liuq fix this.
		return &empty.Empty{}, api.c.StartMining(true, nil)
	}
	return &empty.Empty{}, nil
}

// Stop the miner
func (api *MinerManager) Stop(ctx context.Context, req *empty.Empty) (*pb.IsOk, error) {
	type threaded interface {
		SetThreads(threads int)
	}
	if th, ok := api.c.engine.(threaded); ok {
		th.SetThreads(-1)
	}
	api.c.StopMining()
	return &pb.IsOk{IsOk: true}, nil
}

// SetExtra sets the extra data string that is included when this miner mines a block.
func (api *MinerManager) SetExtra(ctx context.Context, extra *miner.Extra) (*pb.IsOk, error) {
	if err := api.c.Miner().SetExtra([]byte(extra.Extra)); err != nil {
		return &pb.IsOk{IsOk: false}, err
	}
	return &pb.IsOk{IsOk: true}, nil
}

// SetGasPrice sets the minimum accepted gas price for the miner.
func (api *MinerManager) SetGasPrice(ctx context.Context, gasPrice *pb.GasPrice) (*pb.IsOk, error) {
	price := big.NewInt(gasPrice.GasPrice)
	api.c.lock.Lock()
	api.c.gasPrice = price
	api.c.lock.Unlock()

	api.c.txPool.SetGasPrice(price)
	return &pb.IsOk{IsOk: true}, nil
}

// SetChainbase sets the cpcbase of the miner
func (api *MinerManager) SetCoinbase(ctx context.Context, newAddress *pb.Address) (*pb.IsOk, error) {
	api.c.SetCpcbase(common.HexToAddress(newAddress.Address))
	return &pb.IsOk{IsOk: true}, nil
}
