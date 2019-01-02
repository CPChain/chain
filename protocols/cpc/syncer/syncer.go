package syncer

import (
	"errors"
	"math/big"
	"sync/atomic"
	"time"

	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

const (
	SyncTimeout = 5
)

const (
	MaxBlockFetch = 128 // Amount of blocks to be fetched per retrieval request
)

var (
	errBusy         = errors.New("busy")
	errQuitSync     = errors.New("downloader terminated")
	errCanceled     = errors.New("downloader terminated")
	errUnknownPeer  = errors.New("unknown peer")
	errSlowPeer     = errors.New("too slow peer")
	errTimeout      = errors.New("timeout")
	errInvalidChain = errors.New("retrieved invalid chain")
)

// SyncPeer represents a remote peer that i can sync with
type SyncPeer interface {
	ID() string

	// Head returns head block of remote sync peer
	Head() (hash common.Hash, ht *big.Int)

	// SetHead sets head block for remote sync peer
	SetHead(hash common.Hash, ht *big.Int)

	SendGetBlocks(start uint64) error
}

type DropPeer func(id string)

// Syncer will do all sync related works
type Syncer interface {
	// Synchronise syncs blocks from remote peer with given id
	// from current block to latest block with hash as `head`
	// and number as `height`.
	Synchronise(p SyncPeer, head common.Hash, height uint64) error

	// Cancel cancels sync process from remote peer
	Cancel(id string)

	// Synchronising returns if synchronising now
	Synchronising() bool

	// Terminate terminates all sync process and benchmark calculations
	Terminate()

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
	currentPeer    SyncPeer
	dropPeer       DropPeer
	blockchain     BlockChain
	synchronizing  int32 // 0 for false, 1 for true
	syncBlocksCh   chan types.Blocks
	syncRequestsCh chan uint64
	cancelCh       chan struct{}
	quitCh         chan struct{}
}

func New(chain BlockChain, dropPeer DropPeer) *Synchronizer {

	return &Synchronizer{
		blockchain:     chain,
		dropPeer:       dropPeer,
		syncBlocksCh:   make(chan types.Blocks, 1), // there is only one peer to synchronise with.
		syncRequestsCh: make(chan uint64, 1),
		cancelCh:       make(chan struct{}),
		quitCh:         make(chan struct{}),
	}
}

func (s *Synchronizer) Synchronise(p SyncPeer, head common.Hash, height uint64) error {
	switch err := s.synchronise(p, head, height); err {
	case nil, errBusy, errCanceled, errQuitSync:
	case errTimeout, errInvalidChain:

		// TODO: drop peer here
		// drop peer

		return err
	}

	return nil
}
func (s *Synchronizer) synchronise(p SyncPeer, head common.Hash, height uint64) error {
	// if already syncing, return
	if !atomic.CompareAndSwapInt32(&s.synchronizing, 0, 1) {
		return errBusy
	}
	defer atomic.StoreInt32(&s.synchronizing, 0)

	var (
		currentHeader = s.blockchain.CurrentBlock().Header()
		currentNumber = currentHeader.Number.Uint64()
		// currentHash   = currentHeader.Hash()
	)

	// if remote peer is behind us, skip
	if height < currentNumber {
		return errSlowPeer
	}

	s.currentPeer = p
	if s.cancelCh == nil {
		s.cancelCh = make(chan struct{})
	}

	defer s.Cancel(p.ID())

	// fetch blocks with batch size
	for i := currentNumber; i < height; i += MaxBlockFetch {
		timer := time.NewTimer(SyncTimeout * time.Second)

		// this sends sync request
		s.syncRequestsCh <- i

		select {
		case blocks := <-s.syncBlocksCh:
			// handle received blocks
			_, err := s.blockchain.InsertChain(blocks)
			return err

		case <-timer.C:
			return errTimeout

		case <-s.cancelCh:
			return errCanceled

		case <-s.quitCh:
			return errQuitSync
		}
	}

	return nil
}

func (s *Synchronizer) sendRequestLoop() {
	for {
		select {
		case start := <-s.syncRequestsCh:
			s.currentPeer.SendGetBlocks(start)

		case <-s.quitCh:
			return
		}
	}
}

func (s *Synchronizer) Synchronising() bool {
	return atomic.LoadInt32(&s.synchronizing) == 1
}

func (s *Synchronizer) Terminate() {
	if s.quitCh != nil {
		close(s.quitCh)
	}
}

// Cancel cancels sync process from remote peer
func (s *Synchronizer) Cancel(id string) {
	if s.cancelCh != nil {
		close(s.cancelCh)
	}
}

func (s *Synchronizer) DeliverBlocks(id string, blocks types.Blocks) error {
	// if peer id mismatch, return
	if s.currentPeer.ID() != id {
		return errUnknownPeer
	}

	// deliver block
	s.syncBlocksCh <- blocks
	return nil
}
