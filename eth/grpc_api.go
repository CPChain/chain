package eth

import (
	"bytes"
	"compress/gzip"
	"encoding/gob"
	"errors"
	"fmt"
	"io"
	"math/big"
	"os"
	"strings"
	"time"

	"bitbucket.org/cpchain/chain/apis/proto/cpc"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/rawdb"
	"bitbucket.org/cpchain/chain/core/state"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/internal/ethapi"
	"bitbucket.org/cpchain/chain/node/miner"
	"bitbucket.org/cpchain/chain/rpc"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/ethereum/go-ethereum/trie"
	"github.com/golang/protobuf/ptypes/any"
	"github.com/golang/protobuf/ptypes/empty"
	"github.com/golang/protobuf/ptypes/wrappers"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

type PublicEthereumAPIServer struct {
	e *Ethereum
}

func NewPublicEthereumAPIServer(e *Ethereum) *PublicEthereumAPIServer {
	return &PublicEthereumAPIServer{e}
}

func (api *PublicEthereumAPIServer) RegisterServer(s *grpc.Server) {
	protos.RegisterPublicEthereumAPIServer(s, api)
}

func (api *PublicEthereumAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	protos.RegisterPublicEthereumAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

func (api *PublicEthereumAPIServer) Namespace() string {
	return "eth"
}

func (api *PublicEthereumAPIServer) IsPublic() bool {
	return true
}

func (api *PublicEthereumAPIServer) Etherbase(ctx context.Context, e *empty.Empty) (*protos.PublicEthereumAPIReply, error) {
	etherBase, err := api.e.Etherbase()
	if err != nil {
		return nil, err
	}
	return &protos.PublicEthereumAPIReply{Address: &wrappers.BytesValue{Value: etherBase.Bytes()}}, nil
}

func (api *PublicEthereumAPIServer) Coinbase(ctx context.Context, e *empty.Empty) (*protos.PublicEthereumAPIReply, error) {
	return api.Etherbase(ctx, e)
}

func (api *PublicEthereumAPIServer) Hashrate(ctx context.Context, e *empty.Empty) (*protos.PublicEthereumAPIReply, error) {
	rate := api.e.Miner().HashRate()
	return &protos.PublicEthereumAPIReply{Rate: &wrappers.UInt64Value{Value: uint64(rate)}}, nil
}

type PublicMinerAPIServer struct {
	e     *Ethereum
	agent *miner.RemoteAgent
}

func NewPublicMinerAPIServer(e *Ethereum) *PublicMinerAPIServer {
	agent := miner.NewRemoteAgent(e.BlockChain(), e.Engine())
	e.Miner().Register(agent)

	return &PublicMinerAPIServer{e: e, agent: agent}
}

func (api *PublicMinerAPIServer) RegisterServer(s *grpc.Server) {
	protos.RegisterPublicMinerAPIServer(s, api)
}

func (api *PublicMinerAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	protos.RegisterPublicMinerAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

func (api *PublicMinerAPIServer) IsPublic() bool {
	return true
}

func (api *PublicMinerAPIServer) Namespace() string {
	return "eth"
}

func (api *PublicMinerAPIServer) Mining(ctx context.Context, req *empty.Empty) (*protos.PublicMinerAPIReply, error) {
	return &protos.PublicMinerAPIReply{Mining: &wrappers.BoolValue{Value: api.e.IsMining()}}, nil
}

func (api *PublicMinerAPIServer) SubmitWork(ctx context.Context, req *protos.PublicMinerAPIRequest) (*protos.PublicMinerAPIReply, error) {
	var (
		nonce    types.BlockNonce
		digest   common.Hash
		solution common.Hash
	)
	copy(nonce[:], req.BlockNonce.Value)
	digest = common.BytesToHash(req.Digest.Value)
	solution = common.BytesToHash(req.Solution.Value)
	acceped := api.agent.SubmitWork(nonce, digest, solution)
	return &protos.PublicMinerAPIReply{IsAccepting: acceped}, nil
}

func (api *PublicMinerAPIServer) GetWork(ctx context.Context, req *empty.Empty) (*protos.PublicMinerAPIReply, error) {
	if !api.e.IsMining() {
		// TODO: @liuq fix this.
		if err := api.e.StartMining(false, nil); err != nil {
			return &protos.PublicMinerAPIReply{}, err
		}
	}
	work, err := api.agent.GetWork()
	if err != nil {
		return &protos.PublicMinerAPIReply{Works: work[:]}, fmt.Errorf("mining not ready: %v", err)
	}
	return &protos.PublicMinerAPIReply{Works: work[:]}, nil
}

func (api *PublicMinerAPIServer) SubmitHashrate(ctx context.Context, req *protos.PublicMinerAPIRequest) (*protos.PublicMinerAPIReply, error) {
	api.agent.SubmitHashrate(common.BytesToHash(req.Id), req.Hashrate)
	return &protos.PublicMinerAPIReply{IsAccepting: true}, nil
}

// PrivateMinerAPIServer provides private RPC methods to control the miner.
// These methods can be abused by external users and must be considered insecure for use by untrusted users.
type PrivateMinerAPIServer struct {
	e *Ethereum
}

// NewPrivateMinerAPIServer create a new RPC service which controls the miner of this node.
func NewPrivateMinerAPIServer(e *Ethereum) *PrivateMinerAPIServer {
	return &PrivateMinerAPIServer{e: e}
}

func (api *PrivateMinerAPIServer) RegisterServer(s *grpc.Server) {
	protos.RegisterPrivateMinerAPIServer(s, api)
}

func (api *PrivateMinerAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	protos.RegisterPrivateMinerAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

func (api *PrivateMinerAPIServer) IsPublic() bool {
	return false
}

func (api *PrivateMinerAPIServer) Namespace() string {
	return "miner"
}

// Start the miner with the given number of threads. If threads is nil the number
// of workers started is equal to the number of logical CPUs that are usable by
// this process. If mining is already running, this method adjust the number of
// threads allowed to use.
func (api *PrivateMinerAPIServer) Start(ctx context.Context, req *protos.PrivateMinerAPIRequest) (*protos.PrivateMinerAPIReply, error) {
	// Set the number of threads if the seal engine supports it
	if req.Threads == nil {
		req.Threads = &wrappers.Int32Value{}
	} else if req.Threads.Value == 0 {
		req.Threads.Value = -1
	}
	type threaded interface {
		SetThreads(threads int)
	}
	if th, ok := api.e.engine.(threaded); ok {
		log.Info("Updated mining threads", "threads", req.Threads)
		th.SetThreads(int(req.Threads.Value))
	}
	// Start the miner and return
	if !api.e.IsMining() {
		// Propagate the initial price point to the transaction pool
		api.e.lock.RLock()
		price := api.e.gasPrice
		api.e.lock.RUnlock()

		api.e.txPool.SetGasPrice(price)
		// TODO: @liuq fix this.
		return &protos.PrivateMinerAPIReply{}, api.e.StartMining(true, nil)
	}
	return &protos.PrivateMinerAPIReply{}, nil
}

// Stop the miner
func (api *PrivateMinerAPIServer) Stop(ctx context.Context, req *empty.Empty) (*protos.PrivateMinerAPIReply, error) {
	type threaded interface {
		SetThreads(threads int)
	}
	if th, ok := api.e.engine.(threaded); ok {
		th.SetThreads(-1)
	}
	api.e.StopMining()
	return &protos.PrivateMinerAPIReply{IsOk: true}, nil
}

// SetExtra sets the extra data string that is included when this miner mines a block.
func (api *PrivateMinerAPIServer) SetExtra(ctx context.Context, req *protos.PrivateMinerAPIRequest) (*protos.PrivateMinerAPIReply, error) {
	if err := api.e.Miner().SetExtra([]byte(req.Extra)); err != nil {
		return &protos.PrivateMinerAPIReply{IsOk: false}, err
	}
	return &protos.PrivateMinerAPIReply{IsOk: true}, nil
}

// SetGasPrice sets the minimum accepted gas price for the miner.
func (api *PrivateMinerAPIServer) SetGasPrice(ctx context.Context, req *protos.PrivateMinerAPIRequest) (*protos.PrivateMinerAPIReply, error) {
	gasPrice := new(big.Int).SetBytes(req.GasPrice)
	api.e.lock.Lock()
	api.e.gasPrice = gasPrice
	api.e.lock.Unlock()

	api.e.txPool.SetGasPrice(gasPrice)
	return &protos.PrivateMinerAPIReply{IsOk: true}, nil
}

// SetEtherbase sets the etherbase of the miner
func (api *PrivateMinerAPIServer) SetEtherbase(ctx context.Context, req *protos.PrivateMinerAPIRequest) (*protos.PrivateMinerAPIReply, error) {
	api.e.SetEtherbase(common.BytesToAddress(req.Etherbase))
	return &protos.PrivateMinerAPIReply{IsOk: true}, nil
}

// GetHashrate returns the current hashrate of the miner.
func (api *PrivateMinerAPIServer) GetHashrate(ctx context.Context, req *empty.Empty) (*protos.PrivateMinerAPIReply, error) {
	return &protos.PrivateMinerAPIReply{Hashrate: uint64(api.e.miner.HashRate())}, nil
}

// PrivateAdminAPI is the collection of Ethereum full node-related APIs
// exposed over the private admin endpoint.
type PrivateAdminAPIServer struct {
	e *Ethereum
}

func NewPrivateAdminAPIServer(e *Ethereum) *PrivateAdminAPIServer {
	return &PrivateAdminAPIServer{e: e}
}

func (api *PrivateAdminAPIServer) RegisterServer(s *grpc.Server) {
	protos.RegisterPrivateAdminAPIServer(s, api)
}

func (api *PrivateAdminAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	protos.RegisterPrivateAdminAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

func (api *PrivateAdminAPIServer) IsPublic() bool {
	return true
}

func (api *PrivateAdminAPIServer) Namespace() string {
	return "admin"
}

// NewPrivateAdminAPI creates a new API definition for the full node private
// admin methods of the Ethereum service.
func (api *PrivateAdminAPIServer) ExportChain(ctx context.Context, req *protos.PrivateAdminAPIRequest) (*protos.PrivateAdminAPIReply, error) {
	// Make sure we can create the file to export into
	out, err := os.OpenFile(req.File, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, os.ModePerm)
	if err != nil {
		return &protos.PrivateAdminAPIReply{IsOk: false}, err
	}
	defer out.Close()

	var writer io.Writer = out
	if strings.HasSuffix(req.File, ".gz") {
		writer = gzip.NewWriter(writer)
		defer writer.(*gzip.Writer).Close()
	}

	// Export the blockchain
	if err := api.e.BlockChain().Export(writer); err != nil {
		return &protos.PrivateAdminAPIReply{IsOk: false}, err
	}
	return &protos.PrivateAdminAPIReply{IsOk: true}, err
}

// ExportChain exports the current blockchain into a local file.
func (api *PrivateAdminAPIServer) ImportChain(ctx context.Context, req *protos.PrivateAdminAPIRequest) (*protos.PrivateAdminAPIReply, error) {
	// Make sure the can access the file to import
	in, err := os.Open(req.File)
	if err != nil {
		return &protos.PrivateAdminAPIReply{IsOk: false}, err
	}
	defer in.Close()

	var reader io.Reader = in
	if strings.HasSuffix(req.File, ".gz") {
		if reader, err = gzip.NewReader(reader); err != nil {
			return &protos.PrivateAdminAPIReply{IsOk: false}, err
		}
	}

	// Run actual the import in pre-configured batches
	stream := rlp.NewStream(reader, 0)

	blocks, index := make([]*types.Block, 0, 2500), 0
	for batch := 0; ; batch++ {
		// Load a batch of blocks from the input file
		for len(blocks) < cap(blocks) {
			block := new(types.Block)
			if err := stream.Decode(block); err == io.EOF {
				break
			} else if err != nil {
				return &protos.PrivateAdminAPIReply{IsOk: false}, fmt.Errorf("block %d: failed to parse: %v", index, err)
			}
			blocks = append(blocks, block)
			index++
		}
		if len(blocks) == 0 {
			break
		}

		if hasAllBlocks(api.e.BlockChain(), blocks) {
			blocks = blocks[:0]
			continue
		}
		// Import the batch and reset the buffer
		if _, err := api.e.BlockChain().InsertChain(blocks); err != nil {
			return &protos.PrivateAdminAPIReply{IsOk: false}, fmt.Errorf("batch %d: failed to insert: %v", batch, err)
		}
		blocks = blocks[:0]
	}
	return &protos.PrivateAdminAPIReply{IsOk: true}, nil
}

// PublicDebugAPIServer is the collection of Ethereum full node APIs exposed
// over the public debugging endpoint.
type PublicDebugAPIServer struct {
	e *Ethereum
}

// NewPublicDebugAPIServer creates a new API definition for the full node-
// related public debug methods of the Ethereum service.
func NewPublicDebugAPIServer(e *Ethereum) *PublicDebugAPIServer {
	return &PublicDebugAPIServer{e: e}
}

func (api *PublicDebugAPIServer) RegisterServer(s *grpc.Server) {
	protos.RegisterPublicDebugAPIServer(s, api)
}

func (api *PublicDebugAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	protos.RegisterPublicDebugAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

func (api *PublicDebugAPIServer) IsPublic() bool {
	return true
}

func (api *PublicDebugAPIServer) Namespace() string {
	return "debug"
}

// DumpBlock retrieves the entire state of the database at a given block.
// TODO: @sangh
func (api *PublicDebugAPIServer) DumpBlock(ctx context.Context, req *protos.PublicDebugAPIRequest) (*any.Any, error) {
	f := func(dump *state.Dump) (*any.Any, error) {
		var buf bytes.Buffer
		enc := gob.NewEncoder(&buf)
		if err := enc.Encode(&dump); err != nil {
			return &any.Any{}, err
		}
		return &any.Any{Value: buf.Bytes()}, nil
	}
	blockNumber := rpc.BlockNumber(req.BlockNumber)
	if blockNumber == rpc.PendingBlockNumber {
		// If we're dumping the pending state, we need to request
		// both the pending block as well as the pending state from
		// the miner and operate on those
		_, stateDb := api.e.miner.Pending()
		dump := stateDb.RawDump()
		return f(&dump)
	}
	var block *types.Block
	if blockNumber == rpc.LatestBlockNumber {
		block = api.e.blockchain.CurrentBlock()
	} else {
		block = api.e.blockchain.GetBlockByNumber(uint64(blockNumber))
	}
	if block == nil {
		return &any.Any{}, fmt.Errorf("block #%d not found", blockNumber)
	}
	stateDb, err := api.e.BlockChain().StateAt(block.StateRoot())
	if err != nil {
		return &any.Any{}, err
	}
	dump := stateDb.RawDump()
	return f(&dump)
}

// PrivateDebugAPI is the collection of Ethereum full node APIs exposed over
// the private debugging endpoint.
type PrivateDebugAPIServer struct {
	config *configs.ChainConfig
	eth    *Ethereum
}

// NewPrivateDebugAPI creates a new API definition for the full node-related
// private debug methods of the Ethereum service.
func NewPrivateDebugAPIServer(config *configs.ChainConfig, eth *Ethereum) *PrivateDebugAPIServer {
	return &PrivateDebugAPIServer{config: config, eth: eth}
}

func (api *PrivateDebugAPIServer) RegisterServer(s *grpc.Server) {
	protos.RegisterPrivateDebugAPIServer(s, api)
}

func (api *PrivateDebugAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	protos.RegisterPrivateDebugAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

func (api *PrivateDebugAPIServer) IsPublic() bool {
	return true
}

func (api *PrivateDebugAPIServer) Namespace() string {
	return "debug"
}

// Preimage is a debug API function that returns the preimage for a sha3 hash, if known.
func (api *PrivateDebugAPIServer) Preimage(ctx context.Context, req *protos.PrivateDebugAPIRequest) (*protos.PrivateDebugAPIReply, error) {
	if preimage := rawdb.ReadPreimage(api.eth.ChainDb(), common.BytesToHash(req.Hash)); preimage != nil {
		return &protos.PrivateDebugAPIReply{Preimage: preimage}, nil
	}
	return nil, errors.New("unknown preimage")
}

func (api *PrivateDebugAPIServer) GetBadBlocks(ctx context.Context, req *protos.PrivateDebugAPIRequest) (*any.Any, error) {
	blocks := api.eth.BlockChain().BadBlocks()
	results := make([]*BadBlockArgs, len(blocks))

	var err error
	for i, block := range blocks {
		results[i] = &BadBlockArgs{
			Hash: block.Hash(),
		}
		if rlpBytes, err := rlp.EncodeToBytes(block); err != nil {
			results[i].RLP = err.Error() // Hacky, but hey, it works
		} else {
			results[i].RLP = fmt.Sprintf("0x%x", rlpBytes)
		}
		if results[i].Block, err = ethapi.RPCMarshalBlock(block, true, true); err != nil {
			results[i].Block = map[string]interface{}{"error": err.Error()}
		}
	}
	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(results); err != nil {
		return &any.Any{}, err
	}
	return &any.Any{Value: buf.Bytes()}, nil
}

// StorageRangeAt returns the storage at the given block height and transaction index.
func (api *PrivateDebugAPIServer) StorageRangeAt(ctx context.Context, req *protos.PrivateDebugAPIRequest) (*any.Any, error) {
	blockHash := common.BytesToHash(req.BlockHash)
	_, _, statedb, err := api.computeTxEnv(blockHash, int(req.TxIndex), 0)
	contractAddress := common.BytesToAddress(req.ContractAddress)
	if err != nil {
		return &any.Any{}, err
	}
	st := statedb.StorageTrie(contractAddress)
	if st == nil {
		return &any.Any{}, fmt.Errorf("account %x doesn't exist", contractAddress)
	}
	result, err := storageRangeAt(st, req.KeyStart, int(req.MaxResult))
	if err != nil {
		return &any.Any{}, err
	}
	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(&result); err != nil {
		return &any.Any{}, err
	}
	return &any.Any{Value: buf.Bytes()}, nil
}

// GetModifiedAccountsByNumber returns all accounts that have changed between the
// two blocks specified. A change is defined as a difference in nonce, balance,
// code hash, or storage hash.
//
// With one parameter, returns the list of accounts modified in the specified block.
func (api *PrivateDebugAPIServer) GetModifiedAccountsByNumber(ctx context.Context, req *protos.PrivateDebugAPIRequest) (*any.Any, error) {
	var startBlock, endBlock *types.Block

	startBlock = api.eth.blockchain.GetBlockByNumber(req.StartNum)
	if startBlock == nil {
		return nil, fmt.Errorf("start block %x not found", req.StartNum)
	}

	if req.EndNum == nil {
		endBlock = startBlock
		startBlock = api.eth.blockchain.GetBlockByHash(startBlock.ParentHash())
		if startBlock == nil {
			return nil, fmt.Errorf("block %x has no parent", endBlock.Number())
		}
	} else {
		endBlock = api.eth.blockchain.GetBlockByNumber(req.EndNum.Value)
		if endBlock == nil {
			return nil, fmt.Errorf("end block %d not found", req.EndNum.Value)
		}
	}
	accounts, err := api.getModifiedAccounts(startBlock, endBlock)
	if err != nil {
		return &any.Any{}, err
	}

	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(accounts); err != nil {
		return &any.Any{}, nil
	}
	return &any.Any{Value: buf.Bytes()}, nil
}

func (api *PrivateDebugAPIServer) GetModifiedAccountsByHash(ctx context.Context, req *protos.PrivateDebugAPIRequest) (*any.Any, error) {
	var startBlock, endBlock *types.Block
	startBlock = api.eth.blockchain.GetBlockByHash(common.BytesToHash(req.StartHash))
	if startBlock == nil {
		return nil, fmt.Errorf("start block %x not found", req.StartHash)
	}

	if req.EndHash == nil {
		endBlock = startBlock
		startBlock = api.eth.blockchain.GetBlockByHash(startBlock.ParentHash())
		if startBlock == nil {
			return nil, fmt.Errorf("block %x has no parent", endBlock.Number())
		}
	} else {
		endBlock = api.eth.blockchain.GetBlockByHash(common.BytesToHash(req.EndHash.Value))
		if endBlock == nil {
			return nil, fmt.Errorf("end block %x not found", req.EndHash.Value)
		}
	}
	accounts, err := api.getModifiedAccounts(startBlock, endBlock)
	if err != nil {
		return &any.Any{}, err
	}

	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(accounts); err != nil {
		return &any.Any{}, nil
	}
	return &any.Any{Value: buf.Bytes()}, nil
}

func (api *PrivateDebugAPIServer) computeStateDB(block *types.Block, reexec uint64) (*state.StateDB, error) {
	// If we have the state fully available, use that
	pubStateDB, err := api.eth.blockchain.StateAt(block.StateRoot())
	if err == nil {
		return pubStateDB, nil
	}
	// Otherwise try to reexec blocks until we find a state or reach our limit
	origin := block.NumberU64()
	database := state.NewDatabase(api.eth.ChainDb())

	for i := uint64(0); i < reexec; i++ {
		block = api.eth.blockchain.GetBlock(block.ParentHash(), block.NumberU64()-1)
		if block == nil {
			break
		}
		if pubStateDB, err = state.New(block.StateRoot(), database); err == nil {
			break
		}
	}
	if err != nil {
		switch err.(type) {
		case *trie.MissingNodeError:
			return nil, errors.New("required historical state unavailable")
		default:
			return nil, err
		}
	}
	// State was available at historical point, regenerate
	var (
		start  = time.Now()
		logged time.Time
		proot  common.Hash
	)
	for block.NumberU64() < origin {
		// Print progress logs if long enough time elapsed
		if time.Since(logged) > 8*time.Second {
			log.Info("Regenerating historical state", "block", block.NumberU64()+1, "target", origin, "elapsed", time.Since(start))
			logged = time.Now()
		}
		// Retrieve the next block to regenerate and process it
		if block = api.eth.blockchain.GetBlockByNumber(block.NumberU64() + 1); block == nil {
			return nil, fmt.Errorf("block #%d not found", block.NumberU64()+1)
		}

		// TODO: check if below statement is correct.
		privStateDB, _ := state.New(core.GetPrivateStateRoot(api.eth.chainDb, block.StateRoot()), pubStateDB.Database())
		// TODO: pass real remote database.
		_, _, _, _, err := api.eth.blockchain.Processor().Process(block, pubStateDB, privStateDB, nil, vm.Config{}, api.eth.blockchain.RsaPrivateKey())
		if err != nil {
			return nil, err
		}
		// Finalize the state so any modifications are written to the trie
		root, err := pubStateDB.Commit(true)
		if err != nil {
			return nil, err
		}
		if err := pubStateDB.Reset(root); err != nil {
			return nil, err
		}
		database.TrieDB().Reference(root, common.Hash{})
		database.TrieDB().Dereference(proot)
		proot = root
	}
	nodes, imgs := database.TrieDB().Size()
	log.Info("Historical state regenerated", "block", block.NumberU64(), "elapsed", time.Since(start), "nodes", nodes, "preimages", imgs)
	return pubStateDB, nil
}

// computeStatePrivDB retrieves the private state database associated with a certain block.
func (api *PrivateDebugAPIServer) computeStatePrivDB(block *types.Block) (*state.StateDB, error) {
	// If we have the state fully available, use that
	privStatedb, err := api.eth.blockchain.StatePrivAt(block.StateRoot())
	if err == nil {
		return privStatedb, nil
	}
	// TODO: Otherwise try to reexec blocks until we find a state or reach our limit
	panic(err)
}

func (api *PrivateDebugAPIServer) computeTxEnv(blockHash common.Hash, txIndex int, reexec uint64) (core.Message, vm.Context, *state.StateDB, error) {
	// Create the parent state database
	block := api.eth.blockchain.GetBlockByHash(blockHash)
	if block == nil {
		return nil, vm.Context{}, nil, fmt.Errorf("block %x not found", blockHash)
	}
	parent := api.eth.blockchain.GetBlock(block.ParentHash(), block.NumberU64()-1)
	if parent == nil {
		return nil, vm.Context{}, nil, fmt.Errorf("parent %x not found", block.ParentHash())
	}
	pubStateDB, err := api.computeStateDB(parent, reexec)
	if err != nil {
		return nil, vm.Context{}, nil, err
	}

	privStateDB, err := api.computeStatePrivDB(parent)
	if err != nil {
		// TODO: log the fatal error
		panic(err)
	}

	// Recompute transactions up to the target index.
	signer := types.MakeSigner(api.config, block.Number())

	for idx, tx := range block.Transactions() {
		// Assemble the transaction call message and return if the requested offset
		msg, _ := tx.AsMessage(signer)
		context := core.NewEVMContext(msg, block.Header(), api.eth.blockchain, nil)

		var statedb *state.StateDB
		if tx.IsPrivate() {
			statedb = privStateDB // replace with private database.
		} else {
			statedb = pubStateDB
		}

		if idx == txIndex {
			return msg, context, statedb, nil
		}

		// Not yet the searched for transaction, execute on top of the current state
		vmenv := vm.NewEVM(context, statedb, api.config, vm.Config{})
		if _, _, _, err := core.ApplyMessage(vmenv, msg, new(core.GasPool).AddGas(tx.Gas())); err != nil {
			return nil, vm.Context{}, nil, fmt.Errorf("tx %x failed: %v", tx.Hash(), err)
		}
		// Ensure any modifications are committed to the state
		statedb.Finalise(true)
	}
	return nil, vm.Context{}, nil, fmt.Errorf("tx index %d out of range for block %x", txIndex, blockHash)
}

func (api *PrivateDebugAPIServer) getModifiedAccounts(startBlock, endBlock *types.Block) ([]common.Address, error) {
	if startBlock.Number().Uint64() >= endBlock.Number().Uint64() {
		return nil, fmt.Errorf("start block height (%d) must be less than end block height (%d)", startBlock.Number().Uint64(), endBlock.Number().Uint64())
	}

	oldTrie, err := trie.NewSecure(startBlock.StateRoot(), trie.NewDatabase(api.eth.chainDb), 0)
	if err != nil {
		return nil, err
	}
	newTrie, err := trie.NewSecure(endBlock.StateRoot(), trie.NewDatabase(api.eth.chainDb), 0)
	if err != nil {
		return nil, err
	}

	diff, _ := trie.NewDifferenceIterator(oldTrie.NodeIterator([]byte{}), newTrie.NodeIterator([]byte{}))
	iter := trie.NewIterator(diff)

	var dirty []common.Address
	for iter.Next() {
		key := newTrie.GetKey(iter.Key)
		if key == nil {
			return nil, fmt.Errorf("no preimage found for hash %x", iter.Key)
		}
		dirty = append(dirty, common.BytesToAddress(key))
	}
	return dirty, nil
}
