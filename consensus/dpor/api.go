package dpor

import (
	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// API is a user facing RPC API to allow controlling the signer and voting
// mechanisms of the proof-of-authority scheme.
type API struct {
	chain consensus.ChainReader
	dpor  *Dpor
	dh    *defaultDporHelper
}

// GetSnapshot retrieves the state Snapshot at a given block.
func (api *API) GetSnapshot(number *rpc.BlockNumber) (*DporSnapshot, error) {
	// Retrieve the requested block number (or current if none requested)
	var header *types.Header
	if number == nil || *number == rpc.LatestBlockNumber {
		header = api.chain.CurrentHeader()
	} else {
		header = api.chain.GetHeaderByNumber(uint64(number.Int64()))
	}
	// Ensure we have an actually valid block and return its Snapshot
	if header == nil {
		return nil, errUnknownBlock
	}
	return api.dpor.dh.snapshot(api.dpor, api.chain, header.Number.Uint64(), header.Hash(), nil)
}

// GetSnapshotAtHash retrieves the state Snapshot at a given block.
func (api *API) GetSnapshotAtHash(hash common.Hash) (*DporSnapshot, error) {
	header := api.chain.GetHeaderByHash(hash)
	if header == nil {
		return nil, errUnknownBlock
	}
	return api.dpor.dh.snapshot(api.dpor, api.chain, header.Number.Uint64(), header.Hash(), nil)
}

// GetSigners retrieves the list of authorized signers at the specified block.
func (api *API) GetSigners(number *rpc.BlockNumber) ([]common.Address, error) {
	// Retrieve the requested block number (or current if none requested)
	var header *types.Header
	if number == nil || *number == rpc.LatestBlockNumber {
		header = api.chain.CurrentHeader()
	} else {
		header = api.chain.GetHeaderByNumber(uint64(number.Int64()))
	}
	// Ensure we have an actually valid block and return the signers from its Snapshot
	if header == nil {
		return nil, errUnknownBlock
	}
	snap, err := api.dpor.dh.snapshot(api.dpor, api.chain, header.Number.Uint64(), header.Hash(), nil)
	if err != nil {
		return nil, err
	}

	return snap.SignersOf(header.Number.Uint64()), nil
}

// GetSignersAtHash retrieves the state Snapshot at a given block.
func (api *API) GetSignersAtHash(hash common.Hash) ([]common.Address, error) {
	header := api.chain.GetHeaderByHash(hash)
	if header == nil {
		return nil, errUnknownBlock
	}
	number := header.Number.Uint64()
	snap, err := api.dpor.dh.snapshot(api.dpor, api.chain, number, hash, nil)
	if err != nil {
		return nil, err
	}
	return snap.SignersOf(number), nil
}
