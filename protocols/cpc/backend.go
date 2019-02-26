// Copyright 2014 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

// Package cpc implements the cpchain protocol.
package cpc

import (
	"fmt"
	"math/big"
	"sync"
	"sync/atomic"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/admission"
	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/rpt_backend_holder"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/bloombits"
	"bitbucket.org/cpchain/chain/core/rawdb"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/internal/cpcapi"
	"bitbucket.org/cpchain/chain/miner"
	"bitbucket.org/cpchain/chain/node"
	"bitbucket.org/cpchain/chain/private"
	"bitbucket.org/cpchain/chain/protocols/cpc/filters"
	"bitbucket.org/cpchain/chain/protocols/cpc/gasprice"
	"bitbucket.org/cpchain/chain/protocols/cpc/syncer"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/event"
	"github.com/ethereum/go-ethereum/p2p"
)

type LesServer interface {
	Start(srvr *p2p.Server)
	Stop()
	Protocols() []p2p.Protocol
	SetBloomBitsIndexer(bbIndexer *core.ChainIndexer)
}

// CpchainService implements the CpchainService full node service.
type CpchainService struct {
	config      *Config
	chainConfig *configs.ChainConfig

	// Channel for shutting down the service
	shutdownChan chan bool // Channel for shutting down the Cpchain

	// Handlers
	txPool          *core.TxPool
	blockchain      *core.BlockChain
	protocolManager *ProtocolManager
	lesServer       LesServer

	server *p2p.Server

	// DB interfaces
	chainDb database.Database // Block chain database

	eventMux       *event.TypeMux
	engine         consensus.Engine
	accountManager *accounts.Manager

	bloomRequests chan chan *bloombits.Retrieval // Channel receiving bloom data retrieval requests
	bloomIndexer  *core.ChainIndexer             // LogsBloom indexer operating during block imports

	// chain service backend
	APIBackend          *APIBackend
	AdmissionApiBackend admission.ApiBackend

	miner    *miner.Miner
	gasPrice *big.Int
	coinbase common.Address

	networkID     uint64
	netRPCService *cpcapi.PublicNetAPI

	lock sync.RWMutex // Protects the variadic fields (e.g. gas price and coinbase)

	remoteDB database.RemoteDatabase // remoteDB represents an remote distributed database.
}

func (s *CpchainService) AddLesServer(ls LesServer) {
	s.lesServer = ls
	ls.SetBloomBitsIndexer(s.bloomIndexer)
}

// New creates a new CpchainService object (including the
// initialisation of the common CpchainService object)
func New(ctx *node.ServiceContext, config *Config) (*CpchainService, error) {
	if !config.SyncMode.IsValid() {
		return nil, fmt.Errorf("invalid sync mode %d", config.SyncMode)
	}
	chainDb, err := CreateDB(ctx, config, "chaindata")
	if err != nil {
		return nil, err
	}
	chainConfig, genesisHash, genesisErr := core.SetupGenesisBlock(chainDb, config.Genesis)
	if _, ok := genesisErr.(*configs.ConfigCompatError); genesisErr != nil && !ok {
		return nil, genesisErr
	}
	log.Info("Initialised chain configuration", "config", chainConfig)

	var remoteDB database.RemoteDatabase
	switch config.PrivateTx.RemoteDBType {
	case private.IPFS:
		remoteDB = database.NewIpfsDB(config.PrivateTx.RemoteDBParams)
	default:
		remoteDB = database.NewIpfsDB(private.DefaultIpfsUrl)
	}

	cpc := &CpchainService{
		config:         config,
		chainDb:        chainDb,
		chainConfig:    chainConfig,
		eventMux:       ctx.EventMux,
		accountManager: ctx.AccountManager,
		shutdownChan:   make(chan bool),
		networkID:      config.NetworkId,
		gasPrice:       config.GasPrice,
		coinbase:       config.Cpcbase,
		bloomRequests:  make(chan chan *bloombits.Retrieval),
		bloomIndexer:   NewBloomIndexer(chainDb, configs.BloomBitsBlocks),
		remoteDB:       remoteDB,
	}

	contractAddrs := configs.ChainConfigInfo().Dpor.Contracts
	cpc.AdmissionApiBackend = admission.NewAdmissionApiBackend(cpc.blockchain, cpc.coinbase,
		contractAddrs[configs.ContractAdmission], contractAddrs[configs.ContractCampaign], contractAddrs[configs.ContractReward])

	cpc.engine = cpc.CreateConsensusEngine(ctx, chainConfig, chainDb, cpc.AdmissionApiBackend)
	log.Info("Initialising cpchain protocol", "versions", ProtocolVersions, "network", config.NetworkId)

	if !config.SkipBcVersionCheck {
		bcVersion := rawdb.ReadDatabaseVersion(chainDb)
		if bcVersion != core.BlockChainVersion && bcVersion != 0 {
			return nil, fmt.Errorf("Blockchain DB version mismatch (%d / %d). Run cpchain upgradedb.\n", bcVersion, core.BlockChainVersion)
		}
		rawdb.WriteDatabaseVersion(chainDb, core.BlockChainVersion)
	}

	var (
		vmConfig    = vm.Config{EnablePreimageRecording: config.EnablePreimageRecording}
		cacheConfig = &core.CacheConfig{Disabled: config.NoPruning, TrieNodeLimit: config.TrieCache, TrieTimeLimit: config.TrieTimeout}
	)
	cpc.blockchain, err = core.NewBlockChain(chainDb, cacheConfig, cpc.chainConfig, cpc.engine, vmConfig, remoteDB, ctx.AccountManager)
	if err != nil {
		return nil, err
	}

	// Rewind the chain in case of an incompatible config upgrade.
	if compat, ok := genesisErr.(*configs.ConfigCompatError); ok {
		log.Warn("Rewinding chain to upgrade configuration", "err", compat)
		cpc.blockchain.SetHead(compat.RewindTo)
		rawdb.WriteChainConfig(chainDb, genesisHash, chainConfig)
	}
	cpc.bloomIndexer.Start(cpc.blockchain)

	if config.TxPool.Journal != "" {
		config.TxPool.Journal = ctx.ResolvePath(config.TxPool.Journal)
	}
	cpc.txPool = core.NewTxPool(config.TxPool, cpc.chainConfig, cpc.blockchain)

	if cpc.protocolManager, err = NewProtocolManager(cpc.chainConfig, config.SyncMode, config.NetworkId, cpc.eventMux, cpc.txPool, cpc.engine, cpc.blockchain, chainDb, cpc.coinbase); err != nil {
		return nil, err
	}

	cpc.miner = miner.New(cpc, cpc.chainConfig, cpc.EventMux(), cpc.engine)

	cpc.APIBackend = &APIBackend{cpc, nil}

	// gas related
	gpoParams := config.GPO
	if gpoParams.Default == nil {
		gpoParams.Default = config.GasPrice
	}
	cpc.APIBackend.gpo = gasprice.NewOracle(cpc.APIBackend, gpoParams)

	contractClient := cpcapi.NewPublicBlockChainAPI(cpc.APIBackend)
	rpt_backend_holder.GetApiBackendHolderInstance().Init(cpc.APIBackend, contractClient)
	return cpc, nil
}

// CreateDB creates the chain database.
func CreateDB(ctx *node.ServiceContext, config *Config, name string) (database.Database, error) {
	db, err := ctx.OpenDatabase(name, config.DatabaseCache, config.DatabaseHandles)
	if err != nil {
		return nil, err
	}
	return db, nil
}

// SetAsMiner sets dpor engine as miner
func (s *CpchainService) SetAsMiner(isMiner bool) {
	if dpor, ok := s.engine.(*dpor.Dpor); ok {
		dpor.SetAsMiner(isMiner)
	}
}

// CreateConsensusEngine creates the required type of consensus engine instance for an Cpchain service
func (s *CpchainService) CreateConsensusEngine(ctx *node.ServiceContext, chainConfig *configs.ChainConfig,
	db database.Database, ac admission.ApiBackend) consensus.Engine {
	eb, err := s.Coinbase()
	if err != nil {
		log.Debug("coinbase is not set, but is allowed for non-miner node", "error", err)
	}
	// If Dpor is requested, set it up
	if chainConfig.Dpor != nil {
		// TODO: fix this. @liuq
		dpor := dpor.New(chainConfig.Dpor, db, ac)
		if eb != (common.Address{}) {
			wallet, err := s.accountManager.Find(accounts.Account{Address: eb})
			if wallet == nil || err != nil {
				log.Error("Etherbase account unavailable locally", "err", err)
				return nil
			}
			dpor.Authorize(eb, wallet.SignHash)
		}
		return dpor
	}
	return nil
}

// APIs return the collection of RPC services the cpc package offers.
// NOTE, some of these services probably need to be moved to somewhere else.
func (s *CpchainService) APIs() []rpc.API {
	apis := cpcapi.GetAPIs(s.APIBackend)

	// Append any APIs exposed explicitly by the consensus engine
	apis = append(apis, s.engine.APIs(s.BlockChain())...)

	// Append any APIs exposed explicitly by the admission control
	apis = append(apis, s.AdmissionApiBackend.Apis()...)

	// Append all the local APIs and return
	return append(apis, []rpc.API{
		{
			Namespace: "eth",
			Version:   "1.0",
			Service:   NewPublicCpchainAPI(s),
			Public:    true,
		},
		{
			Namespace: "eth",
			Version:   "1.0",
			Service:   NewPublicMinerAPI(s),
			Public:    true,
		},
		// // TODO: fix this @liuq
		{
			Namespace: "eth",
			Version:   "1.0",
			Service:   syncer.NewPublicDownloaderAPI(s.protocolManager.syncer, s.eventMux),
			Public:    true,
		},
		{
			Namespace: "miner",
			Version:   "1.0",
			Service:   NewPrivateMinerAPI(s),
			Public:    false,
		}, {
			Namespace: "eth",
			Version:   "1.0",
			Service:   filters.NewPublicFilterAPI(s.APIBackend, false),
			Public:    true,
		}, {
			Namespace: "admin",
			Version:   "1.0",
			Service:   NewPrivateAdminAPI(s),
		}, {
			Namespace: "debug",
			Version:   "1.0",
			Service:   NewPublicDebugAPI(s),
			Public:    true,
		}, {
			Namespace: "debug",
			Version:   "1.0",
			Service:   NewPrivateDebugAPI(s.chainConfig, s),
		}, {
			Namespace: "net",
			Version:   "1.0",
			Service:   s.netRPCService,
			Public:    true,
		},
	}...)
}

func (s *CpchainService) ResetWithGenesisBlock(gb *types.Block) {
	s.blockchain.ResetWithGenesisBlock(gb)
}

func (s *CpchainService) Coinbase() (coinbase common.Address, err error) {
	s.lock.RLock()
	coinbase = s.coinbase
	s.lock.RUnlock()

	if coinbase != (common.Address{}) {
		return coinbase, nil
	}
	if wallets := s.AccountManager().Wallets(); len(wallets) > 0 {
		if accs := wallets[0].Accounts(); len(accs) > 0 {
			coinbase = accs[0].Address

			s.lock.Lock()
			s.coinbase = coinbase
			s.lock.Unlock()

			log.Info("Coinbase automatically configured", "address", coinbase)
			return coinbase, nil
		}
	}
	return common.Address{}, fmt.Errorf("coinbase must be explicitly specified")
}

// SetCoinbase sets the mining reward address.
func (s *CpchainService) SetCoinbase(coinbase common.Address) {
	s.lock.Lock()
	s.coinbase = coinbase
	s.lock.Unlock()

	s.miner.SetCoinbase(coinbase)
}

func (s *CpchainService) SetClientForDpor(client backend.ClientBackend) {
	if dpor, ok := s.engine.(*dpor.Dpor); ok {
		dpor.SetClient(client)
		return
	}
	panic("must set dpor consensus engine")
}

func (s *CpchainService) StartMining(local bool, client backend.ClientBackend) error {
	if s.IsMining() {
		return nil
	}

	coinbase, err := s.Coinbase()
	if err != nil {
		log.Error("Cannot start mining without coinbase", "err", err)
		return fmt.Errorf("coinbase missing: %v", err)
	}

	// post-requisite: miner.isMining == true && dpor.IsMiner() == true && dpor.isToCampaign == true
	if dpor, ok := s.engine.(*dpor.Dpor); ok {
		if dpor.Coinbase() != coinbase {
			wallet, err := s.accountManager.Find(accounts.Account{Address: coinbase})
			if wallet == nil || err != nil {
				log.Error("Etherbase account unavailable locally", "err", err)
				return nil
			}
			dpor.Authorize(coinbase, wallet.SignHash)
		}

		log.Debug("server.nodeid", "enode", s.server.NodeInfo().Enode)

		dpor.SetToCampaign(true)

		// make sure dpor.StartMining start once
		dpor.SetAsMiner(true)
		dpor.SetClient(client)
		go dpor.StartMining(s.blockchain, s.server, s.protocolManager.BroadcastBlock, s.protocolManager.SyncFromPeer, s.protocolManager.SyncFromBestPeer)
		log.Info("start participating campaign", "campaign", dpor.IsToCampaign())
	}

	// Propagate the initial price point to the transaction pool
	s.lock.RLock()
	price := s.gasPrice
	s.lock.RUnlock()

	s.txPool.SetGasPrice(price)

	if local {
		// If local (CPU) mining is started, we can disable the transaction rejection
		// mechanism introduced to speed sync times. CPU mining on mainnet is ludicrous
		// so none will ever hit this path, whereas marking sync done on CPU mining
		// will ensure that private networks work in single miner mode too.
		atomic.StoreUint32(&s.protocolManager.acceptTxs, 1)
	}

	// make sure miner.Start() start once
	if !s.miner.IsMining() {
		go s.miner.Start(coinbase)
	}
	return nil
}

func (s *CpchainService) StopMining() {
	if !s.IsMining() {
		return
	}

	if dpor, ok := s.engine.(*dpor.Dpor); ok {
		// for dpor, keep miner mining, just stop participating campaign
		dpor.SetToCampaign(false)
		log.Info("stopped participating campaign", "campaign", dpor.IsToCampaign())
	} else {
		s.miner.Stop()
	}
}

func (s *CpchainService) IsMining() bool {
	// post-requisite: miner.isMining == true && dpor.IsMiner() == true && dpor.isToCampaign == true
	if dpor, ok := s.engine.(*dpor.Dpor); ok {
		return s.miner.IsMining() && dpor.IsMiner() && dpor.IsToCampaign()
	} else {
		return s.miner.IsMining()
	}
}

func (s *CpchainService) Miner() *miner.Miner { return s.miner }

func (s *CpchainService) AccountManager() *accounts.Manager { return s.accountManager }
func (s *CpchainService) BlockChain() *core.BlockChain      { return s.blockchain }
func (s *CpchainService) TxPool() *core.TxPool              { return s.txPool }
func (s *CpchainService) EventMux() *event.TypeMux          { return s.eventMux }
func (s *CpchainService) Engine() consensus.Engine          { return s.engine }
func (s *CpchainService) ChainDb() database.Database        { return s.chainDb }
func (s *CpchainService) IsListening() bool                 { return true }                                           // Always listening
func (s *CpchainService) CpcVersion() int                   { return int(s.protocolManager.SubProtocols[0].Version) } // the first protocol is the latest version.
func (s *CpchainService) NetVersion() uint64                { return s.networkID }
func (s *CpchainService) Downloader() syncer.Syncer {
	//TODO: fix this @liuq
	return s.protocolManager.syncer
}
func (s *CpchainService) RemoteDB() database.RemoteDatabase { return s.remoteDB }

// Protocols implements node.Service, returning all the currently configured
// network protocols to start.
func (s *CpchainService) Protocols() []p2p.Protocol {
	if s.lesServer == nil {
		return s.protocolManager.SubProtocols
	}
	return append(s.protocolManager.SubProtocols, s.lesServer.Protocols()...)
}

// start implements node.service, starting all internal goroutines needed by the
// cpchain protocol implementation.
func (s *CpchainService) Start(srvr *p2p.Server) error {
	// Start the bloom bits servicing goroutines
	s.startBloomHandlers()

	// Start the RPC service
	s.netRPCService = cpcapi.NewPublicNetAPI(srvr, s.NetVersion())

	s.server = srvr

	log.Info("CpchainService started")

	// Figure out a max peers count based on the server limits
	maxPeers := srvr.MaxPeers
	if s.config.LightServ > 0 {
		if s.config.LightPeers >= srvr.MaxPeers {
			return fmt.Errorf("invalid peer config: light peer count (%d) >= total peer count (%d)", s.config.LightPeers, srvr.MaxPeers)
		}
		maxPeers -= s.config.LightPeers
	}
	// start the networking layer and the light server if requested
	// by this time, the p2p has already started.  we are only starting the upper layer handling.
	s.protocolManager.Start(maxPeers)
	if s.lesServer != nil {
		s.lesServer.Start(srvr)
	}

	return nil
}

// Stop implements node.Service, terminating all internal goroutines used by the
// cpchain protocol.
func (s *CpchainService) Stop() error {
	s.bloomIndexer.Close()
	s.blockchain.Stop()
	s.protocolManager.Stop()
	if s.lesServer != nil {
		s.lesServer.Stop()
	}
	s.txPool.Stop()
	s.miner.Stop()
	s.eventMux.Stop()

	s.chainDb.Close()
	close(s.shutdownChan)

	return nil
}
