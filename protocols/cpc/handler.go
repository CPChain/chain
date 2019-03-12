// Copyright 2018 The cpchain authors
// Copyright 2015 The go-ethereum Authors

package cpc

import (
	"encoding/json"
	"errors"
	"fmt"
	"math"
	"math/big"
	"sync"
	"sync/atomic"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/protocols/cpc/downloader"
	"bitbucket.org/cpchain/chain/protocols/cpc/fetcher"
	"bitbucket.org/cpchain/chain/protocols/cpc/syncer"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/event"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
	"github.com/ethereum/go-ethereum/rlp"
)

const (
	softResponseLimit = 2 * 1024 * 1024 // Target maximum size of returned blocks, headers or node data.
	estHeaderRlpSize  = 500             // Approximate size of an RLP encoded block header

	// txChanSize is the size of channel listening to NewTxsEvent.
	// The number is referenced from the size of tx pool.
	txChanSize = 4096
)

var (
	// errIncompatibleConfig is returned if the requested protocols and configs are
	// not compatible (low protocol version restrictions and high requirements).
	errIncompatibleConfig = errors.New("incompatible configuration")

	errBadEngine = errors.New("bad engine")
)

func errResp(code errCode, format string, v ...interface{}) error {
	return fmt.Errorf("%v - %v", code, fmt.Sprintf(format, v...))
}

type ProtocolManager struct {
	networkID uint64

	fastSync  uint32 // whether fast sync is enabled (gets disabled if we already have blocks)
	acceptTxs uint32 // whether we're considered synchronised (enables transaction processing)

	txpool      txPool
	blockchain  *core.BlockChain
	chainconfig *configs.ChainConfig
	maxPeers    int

	// downloader *downloader.Downloader
	syncer syncer.Syncer

	fetcher *fetcher.Fetcher
	peers   *peerSet

	SubProtocols []p2p.Protocol

	eventMux      *event.TypeMux
	txsCh         chan core.NewTxsEvent // subscribes to new transactions from txpool
	txsSub        event.Subscription    // manages txsCh
	minedBlockSub *event.TypeMuxSubscription

	// channels for fetcher, syncer, txsyncLoop
	newPeerCh   chan *peer
	txsyncCh    chan *txsync
	quitSync    chan struct{}
	noMorePeers chan struct{}

	server   *p2p.Server
	engine   consensus.Engine
	coinbase common.Address

	// wait group is used for graceful shutdowns during downloading and processing
	wg sync.WaitGroup
}

// NewProtocolManager returns a new sub protocol manager. The cpchain sub protocol manages peers capable
// with the cpchain network.
func NewProtocolManager(config *configs.ChainConfig, mode downloader.SyncMode, networkID uint64, mux *event.TypeMux, txpool txPool, engine consensus.Engine, blockchain *core.BlockChain, chaindb database.Database, coinbase common.Address) (*ProtocolManager, error) {
	// Create the protocol manager with the base fields
	manager := &ProtocolManager{
		networkID:   networkID,
		eventMux:    mux,
		txpool:      txpool,
		blockchain:  blockchain,
		chainconfig: config,
		peers:       newPeerSet(),
		newPeerCh:   make(chan *peer),
		noMorePeers: make(chan struct{}),
		txsyncCh:    make(chan *txsync),
		quitSync:    make(chan struct{}),

		engine:   engine,
		coinbase: coinbase,
	}

	// initialize a sub-protocol for every implemented version we can handle
	manager.SubProtocols = make([]p2p.Protocol, 0, len(ProtocolVersions))

	for i, version := range ProtocolVersions {
		// compatible; initialise the sub-protocol
		manager.SubProtocols = append(manager.SubProtocols, p2p.Protocol{
			Name:    ProtocolName,
			Version: version,
			Length:  ProtocolLengths[i],
			Run: func(p *p2p.Peer, rw p2p.MsgReadWriter) error {
				return manager.handlePeer(p, rw, version)
			},
			NodeInfo: func() interface{} {
				// TODO: add dpor pbft status to this if dpor is available
				return manager.NodeInfo()
			},
			PeerInfo: func(id discover.NodeID) interface{} {
				if p := manager.peers.Peer(fmt.Sprintf("%x", id[:8])); p != nil {
					return p.Info()
				}
				return nil
			},
		})
	}
	if len(manager.SubProtocols) == 0 {
		return nil, errIncompatibleConfig
	}
	// TODO: fix this
	// downloader
	// manager.downloader = downloader.New(mode, chaindb, manager.eventMux, blockchain, nil, nil)
	// manager.downloader = downloader.New(mode, chaindb, manager.eventMux, blockchain, nil, manager.removePeer)

	manager.syncer = syncer.New(blockchain, manager.removePeer)

	// fetcher specific
	// verifies the header when insert into the chain
	validator := func(header *types.Header, refHeader *types.Header) error {
		return engine.VerifyHeader(blockchain, header, true, refHeader)
	}
	heighter := func() uint64 {
		return blockchain.CurrentBlock().NumberU64()
	}
	inserter := func(blocks types.Blocks) (int, error) {
		// if fast sync is running, deny importing weird blocks
		if atomic.LoadUint32(&manager.fastSync) == 1 {
			log.Warn("Discarded bad propagated block", "number", blocks[0].Number(), "hash", blocks[0].Hash().Hex())
			return 0, nil
		}
		atomic.StoreUint32(&manager.acceptTxs, 1) // Mark initial sync done on any fetcher import
		return manager.blockchain.InsertChain(blocks)
	}
	manager.fetcher = fetcher.New(blockchain.GetBlockByHash, validator, manager.BroadcastBlock, heighter, inserter, manager.removePeer)

	return manager, nil
}

func (pm *ProtocolManager) removePeer(id string) {
	// Short circuit if the peer was already removed
	peer := pm.peers.Peer(id)
	if peer == nil {
		return
	}
	log.Debug("Removing cpchain peer", "peer", id)

	// Unregister the peer from the downloader and cpchain peer set
	// pm.downloader.UnregisterPeer(id)

	if err := pm.peers.Unregister(id); err != nil {
		log.Error("Peer removal failed", "peer", id, "err", err)
	}
	// Hard disconnect at the networking layer
	if peer != nil {
		peer.Peer.Disconnect(p2p.DiscUselessPeer)
	}
}

// Start starts all the blockchain synchronization mechanisms
func (pm *ProtocolManager) Start(maxPeers int) {
	pm.maxPeers = maxPeers

	// broadcast transactions
	pm.txsCh = make(chan core.NewTxsEvent, txChanSize)
	pm.txsSub = pm.txpool.SubscribeNewTxsEvent(pm.txsCh)
	go pm.txBroadcastLoop()

	// broadcast mined blocks
	pm.minedBlockSub = pm.eventMux.Subscribe(core.NewMinedBlockEvent{})
	go pm.minedBroadcastLoop()

	// receives data
	go pm.syncerLoop()
	// sends out data
	go pm.txsyncLoop()

}

// Stop stops all
func (pm *ProtocolManager) Stop() {
	log.Info("Stopping cpchain protocol")

	pm.txsSub.Unsubscribe()        // quits txBroadcastLoop
	pm.minedBlockSub.Unsubscribe() // quits blockBroadcastLoop

	// Quit the sync loop.
	// After this send has completed, no new peers will be accepted.
	pm.noMorePeers <- struct{}{}

	// Quit fetcher, txsyncLoop.
	close(pm.quitSync)

	// Disconnect existing sessions.
	// This also closes the gate for any new registrations on the peer set.
	// sessions which are already established but not added to pm.peers yet
	// will exit when they try to register.
	pm.peers.Close()

	// Wait for all peer handler goroutines and the loops to come down.
	pm.wg.Wait()

	log.Info("Cpchain protocol stopped")
}

func (pm *ProtocolManager) newPeer(pv int, p *p2p.Peer, rw p2p.MsgReadWriter) *peer {
	return newPeer(pv, p, newMeteredMsgWriter(rw))
}

// addPeer is the callback invoked to manage the life cycle of cpchain peer.
// when this function terminates, the peer is disconnected.
func (pm *ProtocolManager) addPeer(p *peer, isMinerOrValidator bool) (bool, error) {
	// ignore maxPeers if this is a trusted peer
	if pm.peers.Len() >= pm.maxPeers && !p.Peer.Info().Network.Trusted {
		return false, p2p.DiscTooManyPeers
	}

	// Execute the cpchain handshake
	var (
		genesis = pm.blockchain.Genesis()
		head    = pm.blockchain.CurrentHeader()
		hash    = head.Hash()
		height  = head.Number
	)

	// Do normal handshake
	remoteIsMiner, err := p.Handshake(pm.networkID, height, hash, genesis.Hash(), isMinerOrValidator)

	if err != nil {
		log.Debug("Cpchain handshake failed", "err", err)
		return false, err
	}

	if rw, ok := p.rw.(*meteredMsgReadWriter); ok {
		rw.Init(p.version)
	}

	// add the peer to peerset
	if err := pm.peers.Register(p); err != nil {
		log.Debug("register new peer ")
		return false, err
	}

	// // Register the peer in the downloader. If the downloader considers it banned, we disconnect
	// if err := pm.downloader.RegisterPeer(p.id, p.version, p); err != nil {
	// 	return false, err
	// }

	log.Debug("Cpchain peer connected", "name", p.Name())

	return remoteIsMiner, nil
}

func (pm *ProtocolManager) handlePeer(p *p2p.Peer, rw p2p.MsgReadWriter, version uint) error {
	var (
		dporEngine         = pm.engine.(*dpor.Dpor)
		isMiner            = dporEngine.IsMiner()
		workAsValidator    = dporEngine.IsValidator()
		dporMode           = dporEngine.Mode()
		dporProtocol       = dporEngine.Protocol()
		isMinerOrValidator = isMiner || workAsValidator
	)

	if dporMode == dpor.NormalMode && isMinerOrValidator && !dporProtocol.Available() {
		log.Warn("dpor handler is not not available now")
		return nil
	}

	// wrap up the peer
	peer := pm.newPeer(int(version), p, rw)

	// either we quit or we wait on accepting a new peer by syncer
	select {
	case pm.newPeerCh <- peer:
		pm.wg.Add(1)
		defer pm.wg.Done()

		log.Debug("received a new peer", "id", p.ID().String(), "addr", p.RemoteAddr().String())

		// add peer to manager.peers, this is for basic msg syncing
		remoteIsMiner, err := pm.addPeer(peer, isMinerOrValidator)
		if err != nil {
			log.Warn("fail to add peer to cpc protocol manager's peer set", "peer.RemoteAddr", peer.RemoteAddr().String(), "peer.id", peer.IDString(), "err", err)
			return err
		}

		// defer to remove the peer
		defer pm.removePeer(peer.id)

		log.Debug("done of handshake with peer", "id", p.ID().String(), "addr", p.RemoteAddr().String())

		// add peer to dpor.handler.dialer.peers, this is for proposers/validators communication
		id, added := common.Address{}.Hex(), false
		if dporMode == dpor.NormalMode && isMinerOrValidator && remoteIsMiner {
			switch id, _, _, err = dporProtocol.AddPeer(int(version), peer.Peer, peer.rw); err {
			case nil:
				added = true
				log.Debug("done of dpor subprotocol handshake with peer", "id", p.ID().String(), "addr", p.RemoteAddr().String(), "coinbase", id)

			default:
				log.Warn("failed to add peer to dpor peer set", "err", err, "coinbase", id, "addr", p.RemoteAddr().String())
				return err
			}
		}

		// defer to remove the peer
		if added {
			defer dporProtocol.RemovePeer(id)
		}

		// send local pending transactions to the peer.
		// new transactions appearing after this will be sent via broadcasts.
		pm.syncTransactions(peer)

		// stuck in the message loop on this peer
		for {
			msg, err := peer.rw.ReadMsg()
			if err != nil {
				log.Warn("err when reading msg", "err", err)
				return err
			}
			defer msg.Discard()

			if msg.Size > ProtocolMaxMsgSize {
				log.Warn("err when checking msg size", "size", msg.Size)
				return errResp(ErrMsgTooLarge, "%v > %v", msg.Size, ProtocolMaxMsgSize)
			}

			switch {
			case backend.IsSyncMsg(msg):
				switch err = pm.handleSyncMsg(msg, peer); err {
				case nil:

				default:
					log.Warn("err when handling sync msg", "err", err)
					return err
				}

			case backend.IsDporMsg(msg) && dporMode == dpor.NormalMode && isMinerOrValidator:
				switch id, err = dporProtocol.HandleMsg(id, int(version), p, rw, msg); err {
				case nil:

				default:
					log.Warn("err when handling dpor msg", "err", err)
					return err
				}

			default:
				log.Warn("unknown msg code", "msg", msg.Code)
			}
		}

	case <-pm.quitSync:
		return p2p.DiscQuitting
	}

}

func (pm *ProtocolManager) handleSyncMsg(msg p2p.Msg, p *peer) error {
	// Handle the message depending on its contents
	switch {
	case msg.Code == StatusMsg:
		// Status messages should never arrive after the handshake
		return errResp(ErrExtraStatusMsg, "uncontrolled status message")

	// Block header query, collect the requested headers and reply
	case msg.Code == GetBlockHeadersMsg:
		// Decode the complex header query
		var query getBlockHeadersData
		if err := msg.Decode(&query); err != nil {
			return errResp(ErrDecode, "%v: %v", msg, err)
		}

		log.Debug("received GetBlockHeadersMsg", "hash", query.Origin.Hash.Hex(), "number", query.Origin.Number)

		hashMode := query.Origin.Hash != (common.Hash{})
		first := true
		maxNonCanonical := uint64(100)

		// Gather headers until the fetch or network limits is reached
		var (
			bytes   common.StorageSize
			headers []*types.Header
			unknown bool
		)
		for !unknown && len(headers) < int(query.Amount) && bytes < softResponseLimit && len(headers) < downloader.MaxHeaderFetch {
			// Retrieve the next header satisfying the query
			var origin *types.Header
			if hashMode {
				if first {
					first = false
					origin = pm.blockchain.GetHeaderByHash(query.Origin.Hash)
					if origin != nil {
						query.Origin.Number = origin.Number.Uint64()
					}
				} else {
					origin = pm.blockchain.GetHeader(query.Origin.Hash, query.Origin.Number)
				}
			} else {
				origin = pm.blockchain.GetHeaderByNumber(query.Origin.Number)
			}
			if origin == nil {
				break
			}
			headers = append(headers, origin)
			bytes += estHeaderRlpSize

			// Advance to the next header of the query
			switch {
			case hashMode && query.Reverse:
				// Hash based traversal towards the genesis block
				ancestor := query.Skip + 1
				if ancestor == 0 {
					unknown = true
				} else {
					query.Origin.Hash, query.Origin.Number = pm.blockchain.GetAncestor(query.Origin.Hash, query.Origin.Number, ancestor, &maxNonCanonical)
					unknown = query.Origin.Hash == common.Hash{}
				}
			case hashMode && !query.Reverse:
				// Hash based traversal towards the leaf block
				var (
					current = origin.Number.Uint64()
					next    = current + query.Skip + 1
				)
				if next <= current {
					infos, _ := json.MarshalIndent(p.Peer.Info(), "", "  ")
					log.Warn("GetBlockHeaders skip overflow attack", "current", current, "skip", query.Skip, "next", next, "attacker", infos)
					unknown = true
				} else {
					if header := pm.blockchain.GetHeaderByNumber(next); header != nil {
						nextHash := header.Hash()
						expOldHash, _ := pm.blockchain.GetAncestor(nextHash, next, query.Skip+1, &maxNonCanonical)
						if expOldHash == query.Origin.Hash {
							query.Origin.Hash, query.Origin.Number = nextHash, next
						} else {
							unknown = true
						}
					} else {
						unknown = true
					}
				}
			case query.Reverse:
				// Number based traversal towards the genesis block
				if query.Origin.Number >= query.Skip+1 {
					query.Origin.Number -= query.Skip + 1
				} else {
					unknown = true
				}

			case !query.Reverse:
				// Number based traversal towards the leaf block
				query.Origin.Number += query.Skip + 1
			}
		}
		return p.SendBlockHeaders(headers)

	case msg.Code == BlockHeadersMsg:
		// // A batch of headers arrived to one of our previous requests
		// var headers []*types.Header
		// if err := msg.Decode(&headers); err != nil {
		// 	return errResp(ErrDecode, "msg %v: %v", msg, err)
		// }

		// log.Debug("received BlockHeadersMsg", "len", len(headers))

		// // Filter out any explicitly requested headers, deliver the rest to the downloader
		// filter := len(headers) == 1
		// if filter {
		// 	// Irrelevant of the fork checks, send the header to the fetcher just in case
		// 	headers = pm.fetcher.FilterHeaders(p.id, headers, time.Now())
		// }
		// if len(headers) > 0 || !filter {
		// 	err := pm.downloader.DeliverHeaders(p.id, headers)
		// 	if err != nil {
		// 		log.Debug("Failed to deliver headers", "err", err)
		// 	}
		// }

	case msg.Code == GetBlockBodiesMsg:
		// Decode the retrieval message
		msgStream := rlp.NewStream(msg.Payload, uint64(msg.Size))
		if _, err := msgStream.List(); err != nil {
			return err
		}
		// Gather blocks until the fetch or network limits is reached
		var (
			hash   common.Hash
			bytes  int
			bodies []rlp.RawValue
		)

		log.Debug("received GetBlockBodiesMsg")

		for bytes < softResponseLimit && len(bodies) < downloader.MaxBlockFetch {
			// Retrieve the hash of the next block
			if err := msgStream.Decode(&hash); err == rlp.EOL {
				break
			} else if err != nil {
				return errResp(ErrDecode, "msg %v: %v", msg, err)
			}
			// Retrieve the requested block body, stopping if enough was found
			if data := pm.blockchain.GetBodyRLP(hash); len(data) != 0 {
				bodies = append(bodies, data)
				bytes += len(data)
			}
		}
		return p.SendBlockBodiesRLP(bodies)

	case msg.Code == BlockBodiesMsg:
		// // A batch of block bodies arrived to one of our previous requests
		// var request blockBodiesData
		// if err := msg.Decode(&request); err != nil {
		// 	log.Warn("decode BlockBodiesMsg failed", "error", err)
		// 	return errResp(ErrDecode, "msg %v: %v", msg, err)
		// }
		// // Deliver them all to the downloader for queuing
		// transactions := make([][]*types.Transaction, len(request))

		// log.Debug("received BlockBodiesMsg", "len", len(request))

		// for i, body := range request {
		// 	transactions[i] = body.Transactions
		// }
		// // Filter out any explicitly requested bodies, deliver the rest to the downloader
		// filter := len(transactions) > 0
		// if filter {
		// 	transactions = pm.fetcher.FilterBodies(p.id, transactions, time.Now())
		// }
		// if len(transactions) > 0 || !filter {
		// 	err := pm.downloader.DeliverBodies(p.id, transactions)
		// 	if err != nil {
		// 		log.Debug("Failed to deliver bodies", "err", err)
		// 	}
		// }

	case msg.Code == GetNodeDataMsg:
		// Decode the retrieval message
		msgStream := rlp.NewStream(msg.Payload, uint64(msg.Size))
		if _, err := msgStream.List(); err != nil {
			return err
		}
		// Gather state data until the fetch or network limits is reached
		var (
			hash  common.Hash
			bytes int
			data  [][]byte
		)

		log.Debug("received GetNodeDataMsg")

		for bytes < softResponseLimit && len(data) < downloader.MaxStateFetch {
			// Retrieve the hash of the next state entry
			if err := msgStream.Decode(&hash); err == rlp.EOL {
				break
			} else if err != nil {
				return errResp(ErrDecode, "msg %v: %v", msg, err)
			}
			// Retrieve the requested state entry, stopping if enough was found
			if entry, err := pm.blockchain.TrieNode(hash); err == nil {
				data = append(data, entry)
				bytes += len(entry)
			}
		}
		return p.SendNodeData(data)

	case msg.Code == NodeDataMsg:
		// // A batch of node state data arrived to one of our previous requests
		// var data [][]byte
		// if err := msg.Decode(&data); err != nil {
		// 	return errResp(ErrDecode, "msg %v: %v", msg, err)
		// }

		// log.Debug("received NodeDataMsg", "len", len(data))

		// // Deliver all to the downloader
		// if err := pm.downloader.DeliverNodeData(p.id, data); err != nil {
		// 	log.Debug("Failed to deliver node state data", "err", err)
		// }

	case msg.Code == GetReceiptsMsg:
		// Decode the retrieval message
		msgStream := rlp.NewStream(msg.Payload, uint64(msg.Size))
		if _, err := msgStream.List(); err != nil {
			return err
		}

		log.Debug("received GetReceiptsMsg")

		// Gather state data until the fetch or network limits is reached
		var (
			hash     common.Hash
			bytes    int
			receipts []rlp.RawValue
		)
		for bytes < softResponseLimit && len(receipts) < downloader.MaxReceiptFetch {
			// Retrieve the hash of the next block
			if err := msgStream.Decode(&hash); err == rlp.EOL {
				break
			} else if err != nil {
				return errResp(ErrDecode, "msg %v: %v", msg, err)
			}
			// Retrieve the requested block's receipts, skipping if unknown to us
			results := pm.blockchain.GetReceiptsByHash(hash)
			if results == nil {
				if header := pm.blockchain.GetHeaderByHash(hash); header == nil || header.ReceiptsRoot != types.EmptyRootHash {
					continue
				}
			}
			// If known, encode and queue for response packet
			if encoded, err := rlp.EncodeToBytes(results); err != nil {
				log.Error("Failed to encode receipt", "err", err)
			} else {
				receipts = append(receipts, encoded)
				bytes += len(encoded)
			}
		}
		return p.SendReceiptsRLP(receipts)

	case msg.Code == ReceiptsMsg:
		// // A batch of receipts arrived to one of our previous requests
		// var receipts [][]*types.Receipt
		// if err := msg.Decode(&receipts); err != nil {
		// 	return errResp(ErrDecode, "msg %v: %v", msg, err)
		// }

		// log.Debug("received ReceiptsMsg", "len")

		// // Deliver all to the downloader
		// if err := pm.downloader.DeliverReceipts(p.id, receipts); err != nil {
		// 	log.Debug("Failed to deliver receipts", "err", err)
		// }

	case msg.Code == NewBlockHashesMsg:
		var announces newBlockHashesData
		if err := msg.Decode(&announces); err != nil {
			return errResp(ErrDecode, "%v: %v", msg, err)
		}

		log.Debug("received NewBlockHashesMsg", "len", len(announces))

		// Mark the hashes as present at the remote node
		for _, block := range announces {
			p.MarkBlock(block.Hash)
		}
		// Schedule all the unknown hashes for retrieval
		unknown := make(newBlockHashesData, 0, len(announces))
		for _, block := range announces {
			if !pm.blockchain.HasBlock(block.Hash, block.Number) {
				unknown = append(unknown, block)
			}
		}
		for _, block := range unknown {
			// use fetcher to retrieve each block
			pm.fetcher.Notify(p.id, block.Hash, block.Number, time.Now(), p.RequestOneHeader, p.RequestBodies)
		}

	case msg.Code == NewBlockMsg:
		// Retrieve and decode the propagated block
		var request newBlockData
		if err := msg.Decode(&request); err != nil {
			return errResp(ErrDecode, "%v: %v", msg, err)
		}
		request.Block.ReceivedAt = msg.ReceivedAt
		request.Block.ReceivedFrom = p

		log.Debug("received NewBlockMsg", "hash", request.Block.Hash().Hex(), "number", request.Block.NumberU64())

		// mark the peer as owning the block and schedule it for import
		p.MarkBlock(request.Block.Hash())
		// notify fetcher to inject the block
		pm.fetcher.Enqueue(p.id, request.Block)
		var (
			trueHead   = request.Block.Hash()
			trueHeight = request.Block.Number()
		)
		// Update the peers total difficulty if better than the previous
		if _, ht := p.Head(); trueHeight.Cmp(ht) > 0 {
			p.SetHead(trueHead, trueHeight)

			currentBlock := pm.blockchain.CurrentBlock()
			if trueHeight.Cmp(currentBlock.Number()) > 0 {
				// bulk sync from the peer
				go pm.synchronize(p)
			}
		}

	case msg.Code == TxMsg:
		// Transactions arrived, make sure we have a valid and fresh chain to handle them
		if atomic.LoadUint32(&pm.acceptTxs) == 0 {
			break
		}
		// Transactions can be processed, parse all of them and deliver to the pool
		var txs []*types.Transaction
		if err := msg.Decode(&txs); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		log.Debug("received TxMsg", "len", len(txs))

		for i, tx := range txs {
			// Validate and mark the remote transaction
			if tx == nil {
				return errResp(ErrDecode, "transaction %d is nil", i)
			}
			p.MarkTransaction(tx.Hash())
		}
		pm.txpool.AddRemotes(txs)

	case msg.Code == GetBlocksMsg:
		// send blocks as requested
		var start uint64
		if err := msg.Decode(&start); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}
		number := pm.blockchain.CurrentBlock().NumberU64()

		log.Debug("received GetBlocksMsg", "start", start)

		if start >= number {
			// TODO: @liuq return useful err type
			return nil
		}

		var (
			end    = uint64(math.Min(float64(start+syncer.MaxBlockFetch), float64(number+1)))
			blocks = make(types.Blocks, int(end-start))
		)

		for i := start; i < end; i++ {
			block := pm.blockchain.GetBlockByNumber(i)
			blocks[i-start] = block
		}
		return p.SendBlocks(blocks)

	case msg.Code == BlocksMsg:
		// deliver to syncer
		var blocks types.Blocks
		if err := msg.Decode(&blocks); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		log.Debug("received BlocksMsg", "len", len(blocks))

		if len(blocks) > syncer.MaxBlockFetch {
			// TODO: @liuq return useful err type
			return nil
		}

		return pm.syncer.DeliverBlocks(p.IDString(), blocks)

	default:
		return errResp(ErrInvalidMsgCode, "%v", msg.Code)
	}
	return nil
}

// NodeInfo represents a short summary of the Cpchain sub-protocol metadata
// known about the host peer.
type NodeInfo struct {
	Network uint64               `json:"network"` // cpchain network ID (1=Frontier, 2=Morden, Ropsten=3, Rinkeby=4)
	Height  *big.Int             `json:"height"`  // height of the host's blockchain
	Genesis common.Hash          `json:"genesis"` // SHA3 hash of the host's genesis block
	Config  *configs.ChainConfig `json:"config"`  // Chain configuration for the fork rules
	Head    common.Hash          `json:"head"`    // SHA3 hash of the host's best owned block
}

// NodeInfo retrieves some protocol metadata about the running host node.
func (pm *ProtocolManager) NodeInfo() *NodeInfo {
	currentBlock := pm.blockchain.CurrentBlock()
	return &NodeInfo{
		Network: pm.networkID,
		Height:  pm.blockchain.CurrentBlock().Number(),
		Genesis: pm.blockchain.Genesis().Hash(),
		Config:  pm.blockchain.Config(),
		Head:    currentBlock.Hash(),
	}
}
