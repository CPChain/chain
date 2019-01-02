package syncer

import (
	"sync/atomic"

	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// SyncPeer represents a remote peer that i can sync with
type SyncPeer interface {
	SendGetBlockHeaders(start uint64, stop uint64) error
	SendGetBlockBodies(start uint64, stop uint64) error
	SendGetBlocks(start uint64, stop uint64) error
}

// Syncer will do all sync related works
type Syncer interface {
	// Synchronise syncs blocks from remote peer with given id
	// from current block to latest block with hash as `head`
	// and number as `height`.
	Synchronise(p SyncPeer, head common.Hash, height uint64) error

	// Cancel cancels sync process from remote peer
	Cancel()

	// Synchronising returns if synchronising now
	Synchronising() bool

	// Terminate terminates all sync process and benchmark calculations
	Terminate()

	// DeliverBlockHeaders delivers block headers from remote peer with id to syncer
	DeliverBlockHeaders(id string, headers []*types.Header) error

	// DeliverBlockBodies delivers block bodies from remote peer with id to syncer
	DeliverBlockBodies(id string, bodies []*types.Body) error

	// DeliverBlocks delivers blocks from remote peer with id to syncer
	DeliverBlocks(id string, blocks []*types.Block) error
}

// BlockChain encapsulates functions required to sync a (full or fast) blockchain.
type BlockChain interface {

	// GetHeaderByHash retrieves a header from the local chain.
	GetHeaderByHash(common.Hash) *types.Header

	// CurrentHeader retrieves the head header from the local chain.
	CurrentHeader() *types.Header

	// HasBlock verifies a block's presence in the local chain.
	HasBlock(common.Hash, uint64) bool

	// GetBlockByHash retrieves a block from the local chain.
	GetBlockByHash(common.Hash) *types.Block

	// CurrentBlock retrieves the head block from the local chain.
	CurrentBlock() *types.Block

	// CurrentFastBlock retrieves the head fast block from the local chain.
	CurrentFastBlock() *types.Block

	// InsertChain inserts a batch of blocks into the local chain.
	InsertChain(types.Blocks) (int, error)
}

// Synchronizer is responsible for syncing local chain to latest block
type Synchronizer struct {
	currentPeer   SyncPeer
	blockchain    BlockChain
	synchronizing int32 // 0 for false, 1 for true
}

func New(chain BlockChain) *Synchronizer {

	return &Synchronizer{
		blockchain: chain,
	}
}

func (s *Synchronizer) Synchronise(p SyncPeer, head common.Hash, height uint64) error {
	// if already syncing, return
	if !atomic.CompareAndSwapInt32(&s.synchronizing, 0, 1) {
		return nil
	}
	defer atomic.StoreInt32(&s.synchronizing, 0)

	var (
	// currentHeader = s.blockchain.CurrentBlock().Header()
	// currentNumber = currentHeader.Number.Uint64()
	// currentHash   = currentHeader.Hash()
	)

	// fetch height

	// find common ancestor

	// fetch blocks

	return nil
}

func (s *Synchronizer) Cancel() {
	panic("not implemented")
}

func (s *Synchronizer) Synchronising() bool {
	return atomic.LoadInt32(&s.synchronizing) == 1
}

func (s *Synchronizer) Terminate() {
	panic("not implemented")
}

func (s *Synchronizer) DeliverBlockHeaders(id string, headers []*types.Header) error {
	panic("not implemented")
}

func (s *Synchronizer) DeliverBlockBodies(id string, bodies []*types.Body) error {
	panic("not implemented")
}

func (s *Synchronizer) DeliverBlocks(id string, blocks []*types.Block) error {
	panic("not implemented")
}
