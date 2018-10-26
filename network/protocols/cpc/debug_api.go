package cpc

import (
    "bitbucket.org/cpchain/chain/api/v1"
    "bitbucket.org/cpchain/chain/core/state"
    "bitbucket.org/cpchain/chain/rpc"
    "bitbucket.org/cpchain/chain/types"
    "context"
    "fmt"
)

// PublicDebugAPI is the collection of Ethereum full node APIs exposed
// over the public debugging endpoint.
type PublicDebugAPI struct {
    eth *CpchainService
}

// NewPublicDebugAPI creates a new API definition for the full node-
// related public debug methods of the Ethereum service.
func NewPublicDebugAPI(eth *CpchainService) *PublicDebugAPI {
    return &PublicDebugAPI{eth: eth}
}

func grpcDumpAccount(dumpAccount state.DumpAccount) *protos.DumpAccount {
    storage := make(map[string]string)
    for k, v := range dumpAccount.Storage {
        storage[k] = v
    }
    return &protos.DumpAccount{
        Balance:dumpAccount.Balance,
        Nonce:dumpAccount.Nonce,
        Root:dumpAccount.Root,
        CodeHash:dumpAccount.CodeHash,
        Code:dumpAccount.Code,
        Storage:storage,
    }
}
func grpcDump(dump state.Dump) *protos.Dump {
    grpcDump := &protos.Dump{
        Root:dump.Root,
    }
    for k, v := range dump.Accounts {
        grpcDump.Accounts[k] = grpcDumpAccount(v)
    }

    return grpcDump
}

// DumpBlock retrieves the entire state of the database at a given block.
func (api *PublicDebugAPI) DumpBlock(ctx context.Context, blockNumber *protos.BlockNumber) (*protos.Dump, error) {
    if rpc.BlockNumber(blockNumber.BlockNumber) == rpc.PendingBlockNumber{
        // If we're dumping the pending state, we need to request
        // both the pending block as well as the pending state from
        // the miner and operate on those
        _, stateDb := api.eth.miner.Pending()
        return grpcDump(stateDb.RawDump()), nil
    }
    var block *types.Block
    if rpc.BlockNumber(blockNumber.BlockNumber)  == rpc.LatestBlockNumber {
        block = api.eth.blockchain.CurrentBlock()
    } else {
        block = api.eth.blockchain.GetBlockByNumber(uint64(blockNumber.BlockNumber))
    }
    if block == nil {
        return &protos.Dump{}, fmt.Errorf("block #%d not found", blockNumber.BlockNumber)
    }
    stateDb, err := api.eth.BlockChain().StateAt(block.StateRoot())
    if err != nil {
        return &protos.Dump{}, err
    }
    return grpcDump(stateDb.RawDump()), nil
}

