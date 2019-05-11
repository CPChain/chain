package syncer

import (
	"errors"
	"math"
	"math/big"
	"reflect"
	"sync"
	"sync/atomic"
	"time"

	cpchain "bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/commons/chainmetrics"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/core/state"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/event"
)

const (
	SyncTimeout      = 60 * time.Second
	SyncStateTimeout = 60 * time.Second
)

const (
	MaxBlockFetch     = 128  // Amount of blocks to be fetched per retrieval request
	MaxHashFetch      = 512  // Amount of hashes to be fetched per retrieval request
	MaxHeaderFetch    = 192  // Amount of block headers to be fetched per retrieval request
	MaxReceiptFetch   = 256  // Amount of transaction receipts to allow fetching per request
	MaxStateFetch     = 384  // Amount of node state values to allow fetching per request
	maxResultsProcess = 2048 // Number of content download results to import at once into the chain
)

var (
	MaxQueueSize  = 200 // Max size of blocks queue
	MinFullBlocks = configs.DefaultFullSyncPivot
)

// SyncMode : Full, Fast
type SyncMode int

// FullSync, FastSync
const (
	FullSync SyncMode = iota // Synchronise the entire blockchain history from full blocks
	FastSync                 // Quickly download the headers, full sync only at the chain head
)

var (
	errBusy             = errors.New("busy")
	errQuitSync         = errors.New("downloader terminated")
	errCanceled         = errors.New("downloader terminated")
	errAlreadyFetching  = errors.New("already fetching blocks from peer")
	errCancelStateFetch = errors.New("state data download canceled (requested)")
	errInvalidChain     = errors.New("retrieved hash chain is invalid")

	ErrUnknownPeer     = errors.New("unknown peer")
	ErrSlowPeer        = errors.New("too slow peer")
	ErrTimeout         = errors.New("timeout")
	ErrInvalidChain    = errors.New("retrieved invalid chain")
	ErrReceiptValidate = errors.New("fastsync: receipts validate failure")
	ErrBodiesValidate  = errors.New("fastsync: bodies validate failure")
)

// SyncPeer represents a remote peer that i can sync with
type SyncPeer interface {
	IDString() string

	// Head returns head block of remote sync peer
	Head() (hash common.Hash, ht *big.Int)

	SendGetBlocks(start uint64) error

	RequestReceipts(hashes []common.Hash) error

	RequestNodeData(hashes []common.Hash) error

	RequestHeadersByNumber(origin uint64, amount int, skip int, reverse bool) error

	RequestBodies([]common.Hash) error
}

type DropPeer func(id string)

// Syncer will do all sync related works
type Syncer interface {
	// Synchronise syncs blocks from remote peer with given id
	// from current block to latest block with hash as `head`
	// and number as `height`.
	Synchronise(p SyncPeer, head common.Hash, height *big.Int, mode SyncMode) error

	// Cancel cancels sync process from remote peer
	Cancel(id string)

	Progress() cpchain.SyncProgress

	// Synchronising returns if synchronising now
	Synchronising() bool

	// Terminate terminates all sync process and benchmark calculations
	Terminate()

	// DeliverBlocks delivers blocks from remote peer with id to syncer
	DeliverBlocks(id string, blocks types.Blocks) error

	// DeliverReceipts delivers blocks from remote peer with id to syncer
	DeliverReceipts(id string, receipts []types.Receipts) error

	// DeliverNodeData injects a new batch of node state data received from a remote node.
	DeliverNodeData(id string, data [][]byte) error

	// DeliverHeaders injects a new batch of block headers received from a remote
	// node into the download schedule.
	DeliverHeaders(id string, headers []*types.Header) error

	// DeliverBodies injects a new batch of block bodies received from a remote node.
	DeliverBodies(id string, transactions [][]*types.Transaction) error

	// AddPeer add the peer to the pool
	AddPeer(p SyncPeer) error

	// RemovePeer remove the peer
	RemovePeer(peer string) error
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

	// GetReceiptsByHash retrieves the receipts for all transactions in a given block.
	GetReceiptsByHash(hash common.Hash) types.Receipts

	// InsertReceiptChain attempts to complete an already existing header chain with
	// transaction and receipt data.
	InsertReceiptChain(blockChain types.Blocks, receiptChain []types.Receipts) (int, error)

	// InsertHeaderChain attempts to insert the given header chain in to the local
	// chain, possibly creating a reorg. If an error is returned, it will return the
	// index number of the failing header as well an error describing what went wrong.
	InsertHeaderChain(chain []*types.Header, checkFreq int) (int, error)

	// State returns a new mutable state(public) based on the current HEAD block.
	// just for test.
	State() (*state.StateDB, error)

	StateAt(root common.Hash) (*state.StateDB, error)

	Database() database.Database

	// TrieNode retrieves a blob of data associated with a trie node (or code hash)
	// either from ephemeral in-memory cache, or from persistent storage.
	TrieNode(hash common.Hash) ([]byte, error)

	// SetSyncMode set syncMode
	SetSyncMode(mode SyncMode)

	// GetHeaderByNumber retrieves a block header from the database by number,
	// caching it (associated with its hash) if found.
	GetHeaderByNumber(number uint64) *types.Header

	// FastSyncCommitHead sets the current head block to the one defined by the hash
	// irrelevant what the chain contents were prior.
	FastSyncCommitHead(hash common.Hash) error
}

// Synchronizer is responsible for syncing local chain to latest block
type Synchronizer struct {
	currentPeer            SyncPeer
	dropPeer               DropPeer
	blockchain             BlockChain
	synchronizing          int32 // 0 for false, 1 for true
	syncBlocksCh           chan types.Blocks
	syncReceiptsCh         chan []types.Receipts
	syncHeadersCh          chan []*types.Header
	syncBodiesCh           chan [][]*types.Transaction
	syncStateDataCh        chan [][]byte
	syncRequestsCh         chan uint64
	syncRequestReceiptsCh  chan []common.Hash
	syncRequestBodiesCh    chan []common.Hash
	syncRequestStateDataCh chan []common.Hash
	cancelCh               chan struct{}
	quitCh                 chan struct{}

	mux *event.TypeMux

	progress     *cpchain.SyncProgress
	progressLock sync.RWMutex

	peers map[string]SyncPeer

	peerMutex         sync.RWMutex
	stateSyncErrCh    chan error
	stateSyncFinishCh chan struct{}
	headerIdle        int32 // Current header activity state of the peer (idle = 0, active = 1)
	blockIdle         int32 // Current block activity state of the peer (idle = 0, active = 1)

	mode                       SyncMode
	modeMutex                  sync.RWMutex
	blocksQueue                *queue
	finishFetch                int32
	sendRequestLoopIdle        int32
	sendRequestLoopFinishCh    chan struct{}
	processFastSyncContentIdle int32
	processFastSyncContentCh   chan struct{}
	currentPeerMutex           sync.RWMutex
}

func New(chain BlockChain, dropPeer DropPeer, mux *event.TypeMux) *Synchronizer {
	return &Synchronizer{
		mux:                        mux,
		blockchain:                 chain,
		dropPeer:                   dropPeer,
		syncBlocksCh:               make(chan types.Blocks, 1), // there is only one peer to synchronise with.
		syncReceiptsCh:             make(chan []types.Receipts, 1),
		syncStateDataCh:            make(chan [][]byte, 1),
		syncHeadersCh:              make(chan []*types.Header, 1),
		syncBodiesCh:               make(chan [][]*types.Transaction, 1),
		syncRequestsCh:             make(chan uint64, 1),
		syncRequestReceiptsCh:      make(chan []common.Hash, 1),
		syncRequestBodiesCh:        make(chan []common.Hash, 1),
		syncRequestStateDataCh:     make(chan []common.Hash, 1),
		cancelCh:                   make(chan struct{}),
		quitCh:                     make(chan struct{}),
		progress:                   &cpchain.SyncProgress{},
		peers:                      map[string]SyncPeer{},
		stateSyncErrCh:             make(chan error),
		stateSyncFinishCh:          make(chan struct{}),
		blocksQueue:                newQueue(MaxQueueSize),
		finishFetch:                0,
		sendRequestLoopIdle:        0,
		sendRequestLoopFinishCh:    make(chan struct{}),
		processFastSyncContentIdle: 0,
		processFastSyncContentCh:   make(chan struct{}),
	}
}

// AddPeer add the peer to the pool
func (s *Synchronizer) AddPeer(p SyncPeer) error {
	s.peerMutex.Lock()
	defer s.peerMutex.Unlock()
	if len(s.peers) <= 25 {
		s.peers[p.IDString()] = p
	}
	return nil
}

// RemovePeer remove the peer
func (s *Synchronizer) RemovePeer(peer string) error {
	s.peerMutex.Lock()
	defer s.peerMutex.Unlock()
	delete(s.peers, peer)
	return nil
}

func (s *Synchronizer) Synchronise(p SyncPeer, head common.Hash, height *big.Int, mode SyncMode) (err error) {
	s.mux.Post(StartEvent{})
	defer func() {
		if err != nil {
			s.mux.Post(FailedEvent{err})
		} else {
			s.mux.Post(DoneEvent{})
		}
	}()

	s.blockchain.SetKnownHead(head, height.Uint64())

	if mode == FastSync {
		current := s.blockchain.CurrentFastBlock().NumberU64()
		if height.Uint64()-current <= uint64(MinFullBlocks) {
			err = s.synchronise(p, head, height.Uint64(), FullSync)
		} else {
			pivot := s.selectPivot(height.Uint64())
			err = s.synchronise(p, head, pivot, mode)
			if err == nil {
				err = s.synchronise(p, head, height.Uint64(), FullSync)
			}
		}
	} else {
		err = s.synchronise(p, head, height.Uint64(), mode)
	}

	switch err {
	case nil, errBusy, errCanceled, errQuitSync:
	case ErrSlowPeer:
		return err

	case ErrTimeout, ErrReceiptValidate:
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

func (s *Synchronizer) selectPivot(height uint64) uint64 {
	if height <= uint64(MinFullBlocks) {
		return height
	}
	pivot := height - uint64(MinFullBlocks)
	return pivot
}

func (s *Synchronizer) blocksHandler(errCh chan error, successCh chan struct{}, mode SyncMode) {
	for {
		if atomic.LoadInt32(&s.finishFetch) == int32(1) && s.blocksQueue.empty() {
			successCh <- struct{}{}
			return
		}
		task, err := s.blocksQueue.get()
		if err != nil {
			if err == ErrTimeout {
				continue
			}
			log.Error("block queue get error", "err", err)
			errCh <- err
			return
		}
		s.progressLock.Lock()
		if mode == FastSync {
			s.progress.CurrentBlock = s.blockchain.CurrentFastBlock().NumberU64()
		} else {
			s.progress.CurrentBlock = s.blockchain.CurrentBlock().NumberU64()
		}
		s.progressLock.Unlock()

		if mode == FullSync {
			if _, err := s.blockchain.InsertChain(task.data.(types.Blocks)); err != nil {
				log.Debug("insert chain", "err", err)
				errCh <- err
				return
			}
		} else {
			var start = time.Now()
			data := task.data.(blocksWithReceipts)
			_, err := s.blockchain.InsertHeaderChain(data.headers, 16)
			if err != nil {
				errCh <- err
				return
			}
			log.Debug("validate and insert headers", "elapsed", common.PrettyDuration(time.Since(start)))
			start = time.Now()
			blocksNew := make([]*types.Block, len(data.headers))
			for i, header := range data.headers {
				blocksNew[i] = types.NewBlockWithHeader(header).WithBody(data.bodies[i])
			}
			if _, err := s.blockchain.InsertReceiptChain(blocksNew, data.receipts); err != nil {
				log.Error("insert receipts error", "err", err)
				errCh <- err
				return
			}
			// send metrics msg to monitor(prometheus)
			if chainmetrics.NeedMetrics() {
				go chainmetrics.ReportBlockNumberGauge("blocknumber", float64(s.blockchain.CurrentFastBlock().NumberU64()))
			}
			log.Debug("insert blocks with receipts", "elapsed", common.PrettyDuration(time.Since(start)))
		}
	}
}

func (s *Synchronizer) synchronise(p SyncPeer, head common.Hash, height uint64, mode SyncMode) error {
	if s.Synchronising() {
		return nil
	}
	s.modeMutex.Lock()
	s.mode = mode
	s.modeMutex.Unlock()
	// if already syncing, return
	if !atomic.CompareAndSwapInt32(&s.synchronizing, 0, 1) {
		return errBusy
	}
	defer atomic.StoreInt32(&s.synchronizing, 0)

	var (
		currentHeader = s.blockchain.CurrentBlock().Header()
		currentNumber = currentHeader.Number.Uint64()
	)

	if mode == FastSync {
		currentHeader = s.blockchain.CurrentFastBlock().Header()
		currentNumber = currentHeader.Number.Uint64()
	}

	log.Debug("local status", "current number", currentNumber)

	// if remote peer is behind us, skip
	if height <= currentNumber {
		return ErrSlowPeer
	}

	log.Info("Synchronization Started", "peer", p.IDString(), "peer.Head", head.Hex(), "peer.height", height, "local height", currentNumber)

	if atomic.CompareAndSwapInt32(&s.sendRequestLoopIdle, 1, 0) {
		timer := time.NewTimer(5 * time.Second)
		select {
		case <-s.sendRequestLoopFinishCh:
		case <-timer.C:
		}
	}
	if atomic.CompareAndSwapInt32(&s.processFastSyncContentIdle, 1, 0) {
		timer := time.NewTimer(5 * time.Second)
		select {
		case <-s.processFastSyncContentCh:
		case <-timer.C:
		}
	}

	s.cancelCh = make(chan struct{})
	defer s.Cancel(p.IDString())

	s.currentPeerMutex.Lock()
	s.currentPeer = p
	s.currentPeerMutex.Unlock()

	s.progressLock.Lock()
	s.progress.CurrentBlock = currentNumber
	s.progress.StartingBlock = currentNumber
	s.progress.PulledStates = currentNumber
	s.progress.HighestBlock = height
	s.progress.KnownStates = height
	s.progressLock.Unlock()

	if atomic.CompareAndSwapInt32(&s.sendRequestLoopIdle, 0, 1) {
		go s.sendRequestLoop()
	}

	errCh := make(chan error)
	successCh := make(chan struct{})

	atomic.StoreInt32(&s.finishFetch, 0)

	// clean queue
	s.blocksQueue.clear()
	go s.blocksHandler(errCh, successCh, mode)

	// sync state data
	// get the latest block
	if mode == FastSync {
		atomic.StoreInt32(&s.headerIdle, 0)
		atomic.StoreInt32(&s.blockIdle, 0)
		if atomic.CompareAndSwapInt32(&s.processFastSyncContentIdle, 0, 1) {
			s.FetchHeaders(height, 1)
			var latestHeader []*types.Header
			timer := time.NewTimer(SyncTimeout)
			select {
			case latestHeader = <-s.syncHeadersCh:
			case <-timer.C:
				return ErrTimeout
			}
			go func(root common.Hash) {
				err := s.processFastSyncContent(root)
				if err != nil {
					errCh <- err
				}
				s.stateSyncFinishCh <- struct{}{}
			}(latestHeader[0].StateRoot)
		}
	}
	// fetch blocks with batch size
	for i := currentNumber + 1; i < height; {
		timer := time.NewTimer(SyncTimeout)

		log.Debug("sending sync request", "start", i)

		var (
			stats = struct {
				fetchHeaderStart   time.Time
				fetchBodiesStart   time.Time
				fetchReceiptsStart time.Time
			}{fetchHeaderStart: time.Now()}
			blocks   types.Blocks
			receipts []types.Receipts
			headers  []*types.Header
			bodies   [][]*types.Transaction
			cnt      int32
		)

		prepare := make(chan bool, 2)

		if mode == FastSync {
			if MaxBlockFetch < height-i {
				go s.FetchHeaders(i, MaxBlockFetch)
			} else {
				go s.FetchHeaders(i, int(height-i)+1)
			}
			atomic.StoreInt32(&s.headerIdle, 0)
			atomic.StoreInt32(&s.blockIdle, 0)
			atomic.StoreInt32(&cnt, 0)
		} else {
			// this sends sync request
			s.syncRequestsCh <- i
		}

		for {
			select {
			case <-prepare:
				// wait the headers and receipts and transactions of this batch are fetched
				if result, cnt, err := s.insertBlocks(p, &cnt, blocks, receipts, headers, bodies); result {
					log.Debug("success insert Blocks!", "count", cnt)
					i += uint64(cnt)
					goto forEnd
				} else if err != nil {
					return err
				}
			case err := <-errCh:
				if err != nil {
					return err
				}
			case headers = <-s.syncHeadersCh:
				// fetched headers
				elapsed := common.PrettyDuration(time.Since(stats.fetchHeaderStart))
				log.Debug("fetch headers", "elapsed", elapsed)

				if mode == FastSync {
					hashes := make([]common.Hash, len(headers))
					for i, header := range headers {
						hashes[i] = header.Hash()
					}
					stats.fetchBodiesStart = time.Now()
					stats.fetchReceiptsStart = time.Now()
					// fetch transactions
					s.syncRequestBodiesCh <- hashes
					// fetch receipts
					s.syncRequestReceiptsCh <- hashes
				}
				// headers are prepared
				prepare <- true
			case bodies = <-s.syncBodiesCh:
				elapsed := common.PrettyDuration(time.Since(stats.fetchBodiesStart))
				log.Debug("fetch bodies", "elapsed", elapsed)
				// validate transactions
				minCnt := math.Min(float64(len(bodies)), float64(len(headers)))
				for i := 0; i < int(minCnt); i++ {
					transactionRoot := types.DeriveSha(types.Transactions(bodies[i]))
					if !reflect.DeepEqual(headers[i].TxsRoot, transactionRoot) {
						return ErrBodiesValidate
					}
				}
				// transactions are prepared
				prepare <- true
			case blocks = <-s.syncBlocksCh:
				err := s.blocksQueue.put(resultTask{blocks})
				if err != nil {
					log.Warn("blocks queue put err", "err", err)
					return err
				}
				i += uint64(MaxBlockFetch)
				goto forEnd
			case receipts = <-s.syncReceiptsCh:
				elapsed := common.PrettyDuration(time.Since(stats.fetchReceiptsStart))
				log.Debug("fetch receipts", "elapsed", elapsed)
				minCnt := math.Min(float64(len(receipts)), float64(len(headers)))
				// validate receipts
				for i := 0; i < int(minCnt); i++ {
					receiptHash := types.DeriveSha(types.Receipts(receipts[i]))
					if !reflect.DeepEqual(headers[i].ReceiptsRoot, receiptHash) {
						return ErrReceiptValidate
					}
				}
				// receipts are prepared
				prepare <- true
				log.Debug("Validation Finish!")
			case <-timer.C:
				log.Warn("sync timeout")
				return ErrTimeout
			case <-s.cancelCh:
				return errCanceled
			case <-s.quitCh:
				return errQuitSync
			}
		}
	forEnd:
	}

	// all batches are finished
	atomic.StoreInt32(&s.finishFetch, 1)
	timer := time.NewTimer(5 * time.Second)
	select {
	case <-successCh:
		// wait blocks handler be success
		if mode == FastSync {
			// wait state sync be finished
			<-s.stateSyncFinishCh
			// commit the pivot point
			if err := s.blockchain.FastSyncCommitHead(s.blockchain.CurrentFastBlock().Hash()); err != nil {
				return err
			}
		}
		return nil
	case err := <-errCh:
		return err
	case <-s.cancelCh:
		return errCanceled
	case <-s.quitCh:
		return errQuitSync
	case <-timer.C:
		return ErrTimeout
	}
}

// insertBlocks return true if insert successful
func (s *Synchronizer) insertBlocks(p SyncPeer, cnt *int32, blocks types.Blocks,
	receipts []types.Receipts, headers []*types.Header, bodies [][]*types.Transaction) (bool, int, error) {
	// handle received blocks
	log.Debug("prepare", "cnt", atomic.LoadInt32(cnt))
	if atomic.LoadInt32(cnt) < 2 {
		atomic.AddInt32(cnt, 1)
		return false, 0, nil
	}
	minCnt := math.Min(float64(len(headers)), float64(len(bodies)))
	minCnt = math.Min(minCnt, float64(len(receipts)))
	receipts = receipts[:int(minCnt)]
	headers = headers[:int(minCnt)]
	bodies = bodies[:int(minCnt)]

	err := s.blocksQueue.put(resultTask{
		blocksWithReceipts{headers, bodies, receipts},
	})
	if err != nil {
		log.Warn("blocks queue put err", "err", err)
		return false, 0, err
	}
	return true, int(minCnt), nil
}

func (s *Synchronizer) sendRequestLoop() {
	for {
		select {
		case start := <-s.syncRequestsCh:
			go s.currentPeer.SendGetBlocks(start)
		case hashes := <-s.syncRequestReceiptsCh:
			go s.currentPeer.RequestReceipts(hashes)
		case hashes := <-s.syncRequestBodiesCh:
			go s.FetchBodies(hashes)
		case hashes := <-s.syncRequestStateDataCh:
			go s.currentPeer.RequestNodeData(hashes)
		case <-s.cancelCh:
			s.sendRequestLoopFinishCh <- struct{}{}
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

// DeliverBlocks delivers blocks from remote peer with id to syncer
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

// DeliverReceipts delivers blocks from remote peer with id to syncer
func (s *Synchronizer) DeliverReceipts(id string, receipts []types.Receipts) error {
	// if peer id mismatch, return
	log.Debug("Deliver Receipts", "id", id)
	if s.Synchronising() {
		// deliver receipts
		if s.currentPeer.IDString() != id {
			return ErrUnknownPeer
		}
		s.syncReceiptsCh <- receipts
		return nil
	}
	return errCanceled
}

// DeliverNodeData injects a new batch of node state data received from a remote node.
func (s *Synchronizer) DeliverNodeData(id string, data [][]byte) error {
	// if peer id mismatch, return
	if s.Synchronising() {
		s.currentPeerMutex.Lock()
		defer s.currentPeerMutex.Unlock()
		if s.currentPeer.IDString() != id {
			return ErrUnknownPeer
		}
		// deliver block
		s.syncStateDataCh <- data
		return nil
	}
	return errCanceled
}

// Progress report the progress
func (s *Synchronizer) Progress() cpchain.SyncProgress {
	s.progressLock.RLock()
	defer s.progressLock.RUnlock()

	return *s.progress
}

// FetchHeaders sends a header retrieval request to the remote peer.
func (s *Synchronizer) FetchHeaders(from uint64, count int) error {
	// Short circuit if the peer is already fetching
	if !atomic.CompareAndSwapInt32(&s.headerIdle, 0, 1) {
		return errAlreadyFetching
	}

	// Issue the header retrieval request (absolut upwards without gaps)
	go s.currentPeer.RequestHeadersByNumber(from, count, 0, false)
	return nil
}

// DeliverHeaders injects a new batch of block headers received from a remote
// node into the download schedule.
func (s *Synchronizer) DeliverHeaders(id string, headers []*types.Header) error {
	if s.Synchronising() {
		s.currentPeerMutex.Lock()
		defer s.currentPeerMutex.Unlock()
		if s.currentPeer.IDString() != id {
			return ErrUnknownPeer
		}
		s.syncHeadersCh <- headers
		return nil
	}
	return errCanceled
}

// FetchBodies sends a block body retrieval request to the remote peer.
func (s *Synchronizer) FetchBodies(hashes []common.Hash) error {
	// Short circuit if the peer is already fetching
	if !atomic.CompareAndSwapInt32(&s.blockIdle, 0, 1) {
		return errAlreadyFetching
	}
	go s.currentPeer.RequestBodies(hashes)

	return nil
}

// DeliverBodies injects a new batch of block bodies received from a remote node.
func (s *Synchronizer) DeliverBodies(id string, transactions [][]*types.Transaction) error {
	if s.Synchronising() {
		if s.currentPeer.IDString() != id {
			return ErrUnknownPeer
		}
		s.syncBodiesCh <- transactions
		return nil
	}
	return errCanceled
}
