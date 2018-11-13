package cpc

import (
	"errors"
	"fmt"

	pb "bitbucket.org/cpchain/chain/api/grpc/v1/common"
	"bitbucket.org/cpchain/chain/api/grpc/v1/debug"
	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/core/rawdb"
	"bitbucket.org/cpchain/chain/core/state"
	"bitbucket.org/cpchain/chain/internal/cpcapi"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/ethereum/go-ethereum/trie"
	"github.com/golang/protobuf/ptypes/empty"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

// DebugDumper is the collection of Ethereum full node APIs exposed
// over the public debugging endpoint.
type DebugDumper struct {
	c *CpchainService
}

// NewDebugDumper creates a new API definition for the full node-
// related public debug methods of the Ethereum service.
func NewDebugDumper(c *CpchainService) *DebugDumper {
	return &DebugDumper{c: c}
}

// IsPublic if public default
func (d *DebugDumper) IsPublic() bool {
	return true
}

// Namespace namespace
func (d *DebugDumper) Namespace() string {
	return "debug"
}

// RegisterServer register api to grpc
func (d *DebugDumper) RegisterServer(s *grpc.Server) {
	debug.RegisterDebugDumperServer(s, d)
}

// RegisterJsonRpc register api to restfull json
func (d *DebugDumper) RegisterJsonRpc(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	debug.RegisterDebugDumperHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

func grpcDumpAccount(dumpAccount state.DumpAccount) *pb.DumpAccount {
	storage := make(map[string]string)
	for k, v := range dumpAccount.Storage {
		storage[k] = v
	}
	return &pb.DumpAccount{
		Balance:  dumpAccount.Balance,
		Nonce:    dumpAccount.Nonce,
		Root:     dumpAccount.Root,
		CodeHash: dumpAccount.CodeHash,
		Code:     dumpAccount.Code,
		Storage:  storage,
	}
}

func grpcDump(dump state.Dump) *pb.Dump {
	grpcDump := &pb.Dump{
		Root: dump.Root,
	}
	grpcDump.Accounts = make(map[string]*pb.DumpAccount)
	for k, v := range dump.Accounts {
		grpcDump.Accounts[k] = grpcDumpAccount(v)
	}

	return grpcDump
}

// DumpBlock retrieves the entire state of the database at a given block.
func (api *DebugDumper) DumpBlock(ctx context.Context, blockNumber *pb.BlockNumber) (*pb.Dump, error) {
	if rpc.BlockNumber(blockNumber.BlockNumber) == rpc.PendingBlockNumber {
		// If we're dumping the pending state, we need to request
		// both the pending block as well as the pending state from
		// the miner and operate on those
		_, stateDb := api.c.miner.Pending()
		return grpcDump(stateDb.RawDump()), nil
	}
	var block *types.Block
	if rpc.BlockNumber(blockNumber.BlockNumber) == rpc.LatestBlockNumber {
		block = api.c.blockchain.CurrentBlock()
	} else {
		block = api.c.blockchain.GetBlockByNumber(uint64(blockNumber.BlockNumber))
	}
	if block == nil {
		return &pb.Dump{}, fmt.Errorf("block #%d not found", blockNumber.BlockNumber)
	}
	stateDb, err := api.c.BlockChain().StateAt(block.StateRoot())
	if err != nil {
		return &pb.Dump{}, err
	}
	return grpcDump(stateDb.RawDump()), nil
}

// DebugManager is the collection of Ethereum full node APIs exposed over
// the private debugging endpoint.
type DebugManager struct {
	c *CpchainService
}

// NewDebugManager creates a new API definition for the full node-related
// private debug methods of the Ethereum service.
func NewDebugManager(c *CpchainService) *DebugManager {
	return &DebugManager{c: c}
}

// IsPublic if public default
func (d *DebugManager) IsPublic() bool {
	return false
}

// Namespace namespace
func (d *DebugManager) Namespace() string {
	return "debug"
}

// RegisterServer register api to grpc
func (d *DebugManager) RegisterServer(s *grpc.Server) {
	debug.RegisterDebugManagerServer(s, d)
}

// RegisterJsonRpc register api to restfull json
func (d *DebugManager) RegisterJsonRpc(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	debug.RegisterDebugManagerHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// Preimage is a debug API function that returns the preimage for a sha3 hash, if known.
func (d *DebugManager) Preimage(ctx context.Context, hash *pb.Hash) (*debug.PreimageValue, error) {
	if preimage := rawdb.ReadPreimage(d.c.ChainDb(), common.HexToHash(hash.Hash)); preimage != nil {
		return &debug.PreimageValue{Preimage: preimage}, nil
	}
	return &debug.PreimageValue{}, errors.New("unknown preimage")
}

// GetBadBlocks returns a list of the last 'bad blocks' that the client has seen on the network
// and returns them as a JSON list of block-hashes
func (d *DebugManager) GetBadBlocks(ctx context.Context, req *empty.Empty) (*pb.BadBlockArgs, error) {
	blocks := d.c.BlockChain().BadBlocks()
	results := make([]*pb.BadBlockArg, len(blocks))

	var err error
	for i, block := range blocks {
		results[i] = &pb.BadBlockArg{
			Hash: block.Hash().Hex(),
		}
		if rlpBytes, err := rlp.EncodeToBytes(block); err != nil {
			results[i].Rlp = err.Error() // Hacky, but hey, it works
		} else {
			results[i].Rlp = fmt.Sprintf("0x%x", rlpBytes)
		}
		if results[i].Block, err = cpcapi.GRPCMarshalBlock(block, true, true); err != nil {
			results[i].Block.Error = err.Error()
		}
	}

	var out pb.BadBlockArgs
	out.BadBlockArgs = make([]*pb.BadBlockArg, 0, len(results))
	out.BadBlockArgs = append(out.BadBlockArgs, results...)
	return &out, nil
}

// StorageRangeAt returns the storage at the given block height and transaction index.
func (d *DebugManager) StorageRangeAt(ctx context.Context, req *debug.DebugManagerRequest) (*debug.StorageRangeResult, error) {
	// _, _, statedb, err := d.computeTxEnv(common.HexToHash(req.BlockHash), int(req.TxIndex), 0)
	// if err != nil {
	//     return &debug.StorageRangeResult{}, err
	// }
	// st := statedb.StorageTrie(common.HexToAddress(req.ContractAddress))
	// if st == nil {
	//     return &debug.StorageRangeResult{}, fmt.Errorf("account %x doesn't exist", common.HexToAddress(req.ContractAddress))
	// }
	// return grpcStorageRangeAt(st, req.KeyStart, int(req.MaxResult))
	return &debug.StorageRangeResult{}, nil
}

func grpcStorageRangeAt(st state.Trie, start []byte, maxResult int) (*debug.StorageRangeResult, error) {
	it := trie.NewIterator(st.NodeIterator(start))
	result := &debug.StorageRangeResult{StorageMap: make(map[string]*debug.StorageEntry)}
	for i := 0; i < maxResult && it.Next(); i++ {
		_, content, _, err := rlp.Split(it.Value)
		if err != nil {
			return &debug.StorageRangeResult{}, err
		}
		e := &debug.StorageEntry{Value: common.BytesToHash(content).Hex()}
		if preimage := st.GetKey(it.Key); preimage != nil {
			preimage := common.BytesToHash(preimage)
			e.Key = preimage.Hex()
		}
		result.StorageMap[common.BytesToHash(it.Key).Hex()] = e
	}
	// Add the 'next key' so clients can continue downloading.
	if it.Next() {
		next := common.BytesToHash(it.Key)
		result.NextKey = next.Hex()
	}
	return result, nil
}

// GetModifiedAccountsByNumber returns all accounts that have changed between the
// two blocks specified. A change is defined as a difference in nonce, balance,
// code hash, or storage hash.
//
// With one parameter, returns the list of accounts modified in the specified block.
func (d *DebugManager) GetModifiedAccountsByNumber(ctx context.Context, req *debug.DebugManagerRequest) (*pb.Addresses, error) {
	var startBlock, endBlock *types.Block

	startBlock = d.c.blockchain.GetBlockByNumber(req.StartNumber)
	if startBlock == nil {
		return &pb.Addresses{}, fmt.Errorf("start block %x not found", req.StartNumber)
	}

	if req.EndNumber == nil {
		endBlock = startBlock
		startBlock = d.c.blockchain.GetBlockByHash(startBlock.ParentHash())
		if startBlock == nil {
			return &pb.Addresses{}, fmt.Errorf("block %x has no parent", endBlock.Number())
		}
	} else {
		endBlock = d.c.blockchain.GetBlockByNumber(req.EndNumber.Value)
		if endBlock == nil {
			return &pb.Addresses{}, fmt.Errorf("end block %d not found", req.EndNumber.Value)
		}
	}
	return d.getModifiedAccounts(startBlock, endBlock)
}

// GetModifiedAccountsByHash returns all accounts that have changed between the
// two blocks specified. A change is defined as a difference in nonce, balance,
// code hash, or storage hash.
//
// With one parameter, returns the list of accounts modified in the specified block.
func (d *DebugManager) GetModifiedAccountsByHash(ctx context.Context, req *debug.DebugManagerRequest) (*pb.Addresses, error) {
	var startBlock, endBlock *types.Block
	startBlock = d.c.blockchain.GetBlockByHash(common.HexToHash(req.StartHash))
	if startBlock == nil {
		return &pb.Addresses{}, fmt.Errorf("start block %s not found", req.StartHash)
	}

	if req.EndHash == nil {
		endBlock = startBlock
		startBlock = d.c.blockchain.GetBlockByHash(startBlock.ParentHash())
		if startBlock == nil {
			return &pb.Addresses{}, fmt.Errorf("block %x has no parent", endBlock.Number())
		}
	} else {
		endBlock = d.c.blockchain.GetBlockByHash(common.HexToHash(req.EndHash.Value))
		if endBlock == nil {
			return &pb.Addresses{}, fmt.Errorf("end block %s not found", req.EndHash.Value)
		}
	}
	return d.getModifiedAccounts(startBlock, endBlock)
}

func (d *DebugManager) getModifiedAccounts(startBlock, endBlock *types.Block) (*pb.Addresses, error) {
	if startBlock.Number().Uint64() >= endBlock.Number().Uint64() {
		return &pb.Addresses{}, fmt.Errorf("start block height (%d) must be less than end block height (%d)", startBlock.Number().Uint64(), endBlock.Number().Uint64())
	}

	oldTrie, err := trie.NewSecure(startBlock.StateRoot(), trie.NewDatabase(d.c.chainDb), 0)
	if err != nil {
		return &pb.Addresses{}, err
	}
	newTrie, err := trie.NewSecure(endBlock.StateRoot(), trie.NewDatabase(d.c.chainDb), 0)
	if err != nil {
		return &pb.Addresses{}, err
	}

	diff, _ := trie.NewDifferenceIterator(oldTrie.NodeIterator([]byte{}), newTrie.NodeIterator([]byte{}))
	iter := trie.NewIterator(diff)

	var dirty = &pb.Addresses{Addresses: make([]string, 0, 0)}
	for iter.Next() {
		key := newTrie.GetKey(iter.Key)
		if key == nil {
			return &pb.Addresses{}, fmt.Errorf("no preimage found for hash %x", iter.Key)
		}
		dirty.Addresses = append(dirty.Addresses, common.BytesToAddress(key).Hex())
	}
	return dirty, nil
}
