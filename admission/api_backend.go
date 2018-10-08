package admission

import (
	"errors"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/contracts/dpor"
	"bitbucket.org/cpchain/chain/core/types"
	"bitbucket.org/cpchain/chain/ethclient"
	"bitbucket.org/cpchain/chain/rpc"
)

// AdmissionControl implements APIBackend API.
type AdmissionControl struct {
	backend         Backend
	config          Config
	address         common.Address
	proofInfo       ProofInfo
	keyStore        *keystore.KeyStore
	chainID         *big.Int
	contractBackend dpor.Backend

	mutex  *sync.RWMutex
	status workStatus
	err    error
	abort  chan struct{}
}

// NewAdmissionControl returns a new Control instance.
func NewAdmissionControl(backend Backend, address common.Address, keyStore *keystore.KeyStore, chainID *big.Int, config Config) *AdmissionControl {
	control := &AdmissionControl{
		backend:  backend,
		address:  address,
		config:   config,
		keyStore: keyStore,
		chainID:  chainID,

		abort:  make(chan struct{}),
		mutex:  new(sync.RWMutex),
		status: AcIdle,
	}

	return control
}

// registerProofWork returns all proof work
func (ac *AdmissionControl) getProofWorks() []ProofWorkBackend {
	block := ac.backend.CurrentBlock()
	proofWork := make([]ProofWorkBackend, 0, 2)
	proofWork = append(proofWork, newCPUWork(ac.config.CPUDifficulty, ac.address, block, ac.config.CPULifeTime))
	proofWork = append(proofWork, newMemoryWork(ac.config.MemoryDifficulty, ac.address, block, ac.config.MemoryLifeTime))
	ac.proofInfo.BlockNumber = block.NumberU64()

	return proofWork
}

// APIs returns the collection of RPC services the admission package offers.
func (ac *AdmissionControl) APIs() []rpc.API {
	return []rpc.API{
		{
			Namespace: "admission",
			Version:   "1.0",
			Service:   ac,
			Public:    false,
		},
	}
}

// Campaign starts running all the proof work to generate the campaign information and waits all proof work done, send msg
func (ac *AdmissionControl) Campaign() {
	ac.mutex.Lock()
	defer ac.mutex.Unlock()

	if ac.status == AcRunning {
		return
	}
	ac.proofInfo.BlockNumber = 0
	ac.proofInfo.CPUNonce = 0
	ac.proofInfo.MemoryNonce = 0
	ac.status = AcRunning
	ac.err = nil

	proofWorks := ac.getProofWorks()
	wg := new(sync.WaitGroup)
	wg.Add(len(proofWorks))
	for _, work := range proofWorks {
		go work.prove(ac.abort, wg)
	}

	go ac.waitSendCampaignMsg(proofWorks, wg)
}

// Abort cancels all the proof work associated to the workType.
func (ac *AdmissionControl) Abort() {
	ac.mutex.RLock()
	defer ac.mutex.RUnlock()
	if ac.status != AcRunning {
		return
	}
	// last time exit normally, close channel to abort all work
	if ac.err == nil {
		close(ac.abort)
	}
	ac.abort = make(chan struct{})
}

// GetProofInfo gets all work proofInfo
func (ac *AdmissionControl) GetProofInfo() ProofInfo {
	ac.mutex.RLock()
	defer ac.mutex.RUnlock()

	return ac.proofInfo
}

// GetStatus gets status of campaign
func (ac *AdmissionControl) GetStatus() (workStatus, error) {
	ac.mutex.RLock()
	defer ac.mutex.RUnlock()

	return ac.status, ac.err
}

// waitSendCampaignMsg waits all proof work done, then sends campaign proofInfo to campaign contract
func (ac *AdmissionControl) waitSendCampaignMsg(proofWorks []ProofWorkBackend, wg *sync.WaitGroup) {
	wg.Wait()

	ac.mutex.Lock()
	defer func(ac *AdmissionControl) {
		ac.status = AcIdle
		ac.mutex.Unlock()
	}(ac)

	for _, work := range proofWorks {
		// if work err then return
		if !work.isOk() {
			ac.err = work.getError()
			return
		}
		switch work.(type) {
		case *cpuWork:
			ac.proofInfo.CPUNonce = work.getProofInfo()
		case *memoryWork:
			ac.proofInfo.MemoryNonce = work.getProofInfo()
		}
	}
	ac.sendCampaignProofInfo()
}

// sendCampaignProofInfo sends proof info to campaign contract
func (ac *AdmissionControl) sendCampaignProofInfo() {
	if ac.contractBackend == nil {
		ac.err = errors.New("contractBackend is nil")
		return
	}

	auth := &bind.TransactOpts{
		From: ac.address,
		Signer: func(signer types.Signer, address common.Address, tx *types.Transaction) (*types.Transaction, error) {
			if address != ac.address {
				return nil, errors.New("not authorized to sign this account")
			}
			// chainID test with all signer
			// FIXME for the current, we use `nil' as the chainId.
			return ac.keyStore.SignTx(accounts.Account{Address: ac.address}, tx, nil)
		},
	}

	auth.Value = big.NewInt(ac.config.Deposit)
	instance, err := dpor.NewCampaign(auth, common.HexToAddress(ac.config.CampaignContractAddress), ac.contractBackend)
	if err != nil {
		ac.err = err
		return
	}

	_, err = instance.ClaimCampaign(big.NewInt(ac.config.NumberOfCampaignTimes), big.NewInt(ac.config.MinimumRpt))
	if err != nil {
		ac.err = err
		return
	}
}

// RegisterInProcHander registers the rpc.Server, handles RPC request to process the API requests in process
func (ac *AdmissionControl) RegisterInProcHander(localRPCServer *rpc.Server) {
	client := rpc.DialInProc(localRPCServer)
	ac.contractBackend = ethclient.NewClient(client)
}
