package syncer

import (
	"errors"
	"math/big"
	"sync"
	"sync/atomic"
	"time"

	cpchain "bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/event"
)

const (
	SyncTimeout = 1 * time.Minute
)

const (
	MaxBlockFetch   = 128 // Amount of blocks to be fetched per retrieval request
	MaxHashFetch    = 512 // Amount of hashes to be fetched per retrieval request
	MaxHeaderFetch  = 192 // Amount of block headers to be fetched per retrieval request
	MaxReceiptFetch = 256 // Amount of transaction receipts to allow fetching per request
	MaxStateFetch   = 384 // Amount of node state values to allow fetching per request
)

var (
	errBusy         = errors.New("busy")
	errQuitSync     = errors.New("downloader terminated")
	errCanceled     = errors.New("downloader terminated")
	ErrUnknownPeer  = errors.New("unknown peer")
	ErrSlowPeer     = errors.New("too slow peer")
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

	Progress() cpchain.SyncProgress

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

	// KnownHead returns hash and number of current head block (maybe not in local chain)
	KnownHead() (common.Hash, uint64)

	// SetKnownHead sets the known head block hash and number
	SetKnownHead(common.Hash, uint64)
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

	mux *event.TypeMux

	progress     *cpchain.SyncProgress
	progressLock sync.RWMutex
}

func New(chain BlockChain, dropPeer DropPeer, mux *event.TypeMux) *Synchronizer {

	return &Synchronizer{
		mux:            mux,
		blockchain:     chain,
		dropPeer:       dropPeer,
		syncBlocksCh:   make(chan types.Blocks, 1), // there is only one peer to synchronise with.
		syncRequestsCh: make(chan uint64, 1),
		cancelCh:       make(chan struct{}),
		quitCh:         make(chan struct{}),
		progress:       &cpchain.SyncProgress{},
	}
}

func (s *Synchronizer) Synchronise(p SyncPeer, head common.Hash, height *big.Int) (err error) {
	s.mux.Post(StartEvent{})
	defer func() {
		if err != nil {
			s.mux.Post(FailedEvent{err})
		} else {
			s.mux.Post(DoneEvent{})
		}
	}()

	s.blockchain.SetKnownHead(head, height.Uint64())

	switch err = s.synchronise(p, head, height.Uint64()); err {
	case nil, errBusy, errCanceled, errQuitSync:
	case ErrSlowPeer:
		return err

	case ErrTimeout:
		// drop peer
		if s.dropPeer != nil {
			s.dropPeer(p.IDString())
		}
		return err

	default:
		// drop peer
		if s.dropPeer != nil {
			s.dropPeer(p.IDString())
		}
		return ErrInvalidChain
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
	)

	// if remote peer is behind us, skip
	if height <= currentNumber {
		return ErrSlowPeer
	}

	log.Debug("Synchronization Started", "peer", p.IDString(), "peer.Head", head.Hex(), "peer.height", height, "local height", currentNumber)

	s.currentPeer = p
	s.cancelCh = make(chan struct{})

	s.progressLock.Lock()
	s.progress.CurrentBlock = currentNumber
	s.progress.StartingBlock = currentNumber
	s.progress.PulledStates = currentNumber
	s.progress.HighestBlock = height
	s.progress.KnownStates = height
	s.progressLock.Unlock()

	go s.sendRequestLoop()

	defer s.Cancel(p.IDString())

	// fetch blocks with batch size
	for i := currentNumber + 1; i < height; i += MaxBlockFetch {
		timer := time.NewTimer(SyncTimeout)

		log.Debug("sending sync request", "start", i)

		// this sends sync request
		s.syncRequestsCh <- i

		select {
		case blocks := <-s.syncBlocksCh:

			log.Debug("received blocks from peer", "id", p.IDString())

			s.progressLock.Lock()
			s.progress.CurrentBlock = s.blockchain.CurrentBlock().NumberU64()
			s.progressLock.Unlock()

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
		return ErrUnknownPeer
	}

	if s.Synchronising() {
		// deliver block
		s.syncBlocksCh <- blocks
		return nil
	}
	return errCanceled
}

func (s *Synchronizer) Progress() cpchain.SyncProgress {
	s.progressLock.RLock()
	defer s.progressLock.RUnlock()

	return *s.progress
}
