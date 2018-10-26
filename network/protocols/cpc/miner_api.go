package cpc

import (
    "bitbucket.org/cpchain/chain/api/v1"
    "bitbucket.org/cpchain/chain/commons/log"
    "github.com/ethereum/go-ethereum/common"
    "github.com/golang/protobuf/ptypes/empty"
    "golang.org/x/net/context"
    "math/big"
)

// MineControl provides private RPC methods to control the miner.
// These methods can be abused by external users and must be considered insecure for use by untrusted users.
type MineControl struct {
    e *CpchainService
}

// NewMineControl create a new RPC service which controls the miner of this node.
func NewMineControl(e *CpchainService) *MineControl {
    return &MineControl{e: e}
}

// Start the miner with the given number of threads. If threads is nil the number
// of workers started is equal to the number of logical CPUs that are usable by
// this process. If mining is already running, this method adjust the number of
// threads allowed to use.
func (api *MineControl) Start(ctx context.Context, threads *protos.Threads) (*empty.Empty, error){
    // Set the number of threads if the seal engine supports it
    if threads == nil {
        threads = new(protos.Threads)
    } else if threads.Threads == 0 {
        threads.Threads = -1 // Disable the miner from within
    }
    type threaded interface {
        SetThreads(threads int)
    }
    if th, ok := api.e.engine.(threaded); ok {
        log.Info("Updated mining threads", "threads", *threads)
        th.SetThreads(int(threads.Threads))
    }
    // Start the miner and return
    if !api.e.IsMining() {
        // Propagate the initial price point to the transaction pool
        api.e.lock.RLock()
        price := api.e.gasPrice
        api.e.lock.RUnlock()

        api.e.txPool.SetGasPrice(price)
        // TODO: @liuq fix this.
        return &empty.Empty{},api.e.StartMining(true, nil)
    }
    return &empty.Empty{}, nil
}

// Stop the miner
func (api *MineControl) Stop(ctx context.Context) (*protos.IsOk, error){
    type threaded interface {
        SetThreads(threads int)
    }
    if th, ok := api.e.engine.(threaded); ok {
        th.SetThreads(-1)
    }
    api.e.StopMining()
    return &protos.IsOk{IsOk:true}, nil
}

// SetExtra sets the extra data string that is included when this miner mines a block.
func (api *MineControl) SetExtra(ctx context.Context, extra *protos.Extra) (*protos.IsOk, error) {
    if err := api.e.Miner().SetExtra([]byte(extra.Extra)); err != nil {
        return &protos.IsOk{IsOk:false}, err
    }
    return &protos.IsOk{IsOk:true}, nil
}

// SetGasPrice sets the minimum accepted gas price for the miner.
func (api *MineControl) SetGasPrice(ctx context.Context, gasPrice *protos.GasPrice) (*protos.IsOk, error){
    api.e.lock.Lock()
    api.e.gasPrice = (*big.Int)(gasPrice.GasPrice)
    api.e.lock.Unlock()

    api.e.txPool.SetGasPrice((*big.Int)(gasPrice))
    return &protos.IsOk{IsOk:true}, nil
}

// SetEtherbase sets the etherbase of the miner
func (api *MineControl) SetCoinbase(ctx context.Context, newAddress *protos.Address) (*protos.IsOk, error){
    api.e.SetEtherbase(common.HexToAddress(newAddress.Address))
    return &protos.IsOk{IsOk:true}, nil
}

