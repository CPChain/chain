package syncer

import (
	"errors"
	"math/big"
	"sync/atomic"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
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
	ErrTimeout      = errors.New("timeout")
	ErrInvalidChain = errors.New("retrieved invalid chain")
)

// SyncPeer represents a remote peer that i can sync with
type SyncPeer interface {
	IDString() string

	// Head returns head block of remote sync peer
	Head() (hash common.Hash, ht *big.Int)

	SendGetBlocks(start uint64) error
}

type DropPeer func(id string)

// Syncer will do all sync related works
type Syncer interface {
	// Synchronise syncs blocks from remote peer with given id
	// from current block to latest block with hash as `head`
	// and number as `height`.
	Synchronise(p SyncPeer, head common.Hash, height *big.Int) error

	// Cancel cancels sync process from remote peer
	Cancel(id string)

	// Synchronising returns if synchronising now
	Synchronising() bool

	// Terminate terminates all sync process and benchmark calculations
	Terminate()

	// DeliverBlocks delivers blocks from remote peer with id to syncer
	DeliverBlocks(id string, blocks types.Blocks) error
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

	GetBlockByNumber(uint64) *types.Block

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

func (s *Synchronizer) Synchronise(p SyncPeer, head common.Hash, height *big.Int) error {
	switch err := s.synchronise(p, head, height.Uint64()); err {
	case nil, errBusy, errCanceled, errQuitSync:
	case ErrTimeout, ErrInvalidChain:

		// drop peer
		if s.dropPeer != nil {
			s.dropPeer(p.IDString())
		}

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

	log.Debug("Synchronization Started", "peer", p.IDString(), "peer.Head", head.Hex(), "peer.height", height)

	var (
		currentHeader = s.blockchain.CurrentBlock().Header()
		currentNumber = currentHeader.Number.Uint64()
		// currentHash   = currentHeader.Hash()
	)

	log.Debug("local status", "current number", currentNumber)

	// if remote peer is behind us, skip
	if height < currentNumber {
		return errSlowPeer
	}

	s.currentPeer = p
	s.cancelCh = make(chan struct{})

	go s.sendRequestLoop()

	defer s.Cancel(p.IDString())

	// fetch blocks with batch size
	for i := currentNumber + 1; i < height; i += MaxBlockFetch {
		timer := time.NewTimer(SyncTimeout * time.Second)

		log.Debug("sending sync request", "start", i)

		// this sends sync request
		s.syncRequestsCh <- i

		select {
		case blocks := <-s.syncBlocksCh:

			log.Debug("received blocks from peer", "id", p.IDString())

			// handle received blocks
			_, err := s.blockchain.InsertChain(blocks)
			if err != nil {
				return err
			}

		case <-timer.C:
			return ErrTimeout

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

		case <-s.cancelCh:
			return

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
	if s.currentPeer.IDString() != id {
		return errUnknownPeer
	}

	// deliver block
	s.syncBlocksCh <- blocks
	return nil
}
