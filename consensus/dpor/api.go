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
func (api *API) GetSnapshot(number rpc.BlockNumber) (*DporSnapshot, error) {
	// Retrieve the requested block number (or current if none requested)
	var header *types.Header
	if number == 0 || number == rpc.LatestBlockNumber {
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

// GetProposers retrieves the Proposers at a given block.
func (api *API) GetProposers(number rpc.BlockNumber) ([]common.Address, error) {
	// Retrieve the requested block number (or current if none requested)
	var header *types.Header
	if number == 0 || number == rpc.LatestBlockNumber {
		header = api.chain.CurrentHeader()
	} else {
		header = api.chain.GetHeaderByNumber(uint64(number.Int64()))
	}
	// Ensure we have an actually valid block and return its Proposers
	if header == nil {
		return nil, errUnknownBlock
	}
	return header.Dpor.Proposers, nil
}

// GetValidators retrieves the Validators at a given block.
func (api *API) GetValidators(number rpc.BlockNumber) ([]common.Address, error) {
	return api.dpor.ValidatorsOf(uint64(number))
}
