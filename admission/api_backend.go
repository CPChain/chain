package admission

import (
	"math/big"
	"os"
	"path/filepath"
	"sync"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/contracts/dpor/contract"
	"bitbucket.org/cpchain/chain/ethclient"
	"bitbucket.org/cpchain/chain/rpc"
)

// AdmissionControl implements APIBackend API.
type AdmissionControl struct {
	backend   Backend
	config    Config
	address   common.Address
	client    *ethclient.Client
	proofInfo ProofInfo

	mutex  *sync.Mutex
	status workStatus
	err    error
	abort  chan struct{}
}

// NewAdmissionControl returns a new Control instance.
func NewAdmissionControl(backend Backend, address common.Address, config Config) *AdmissionControl {
	control := &AdmissionControl{
		backend: backend,
		address: address,
		config:  config,

		abort:  make(chan struct{}),
		mutex:  new(sync.Mutex),
		status: AcIdle,
	}

	return control
}

// registerProofWork returns all proof work
func (ac *AdmissionControl) getProofWorks() []ProofWorkBackend {
	proofWork := make([]ProofWorkBackend, 0, 2)
	proofWork = append(proofWork, newCPUWork(ac.config.CPUDifficulty, ac.address, ac.backend.CurrentBlock(), ac.config.CPULifeTime))
	proofWork = append(proofWork, newMemoryWork(ac.config.MemoryDifficulty, ac.address, ac.backend.CurrentBlock(), ac.config.MemoryLifeTime))

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
	ac.mutex.Lock()
	defer ac.mutex.Unlock()
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
	return ac.proofInfo
}

// GetStatus gets status of campaign
func (ac *AdmissionControl) GetStatus() (workStatus, error) {
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
			ac.proofInfo.CPUProofInfo = work.getProofInfo().(CPUProofInfo)
		case *memoryWork:
			ac.proofInfo.MemoryProofInfo = work.getProofInfo().(MemoryProofInfo)
		}
	}
	ac.sendCampaignProofInfo()
}

// waitSendCampaignProofInfo sends proof info to campaign contract
func (ac *AdmissionControl) sendCampaignProofInfo() {
	instance, err := contract.NewCampaign(common.HexToAddress(ac.config.CampaignContractAddress), ac.client)
	if err != nil {
		ac.err = err
		return
	}

	file, _ := os.Open(keystonePath)
	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	if err != nil {
		ac.err = err
		return
	}
	kst := keystore.NewKeyStore(keyPath, 2, 1)
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, "passwd")
	if err != nil {
		ac.err = err
		return
	}

	auth := bind.NewKeyedTransactor(key.PrivateKey)
	if err != nil {
		ac.err = err
		return
	}

	_, err = instance.ClaimCampaign(auth, big.NewInt(int64(numOfCampaign)), big.NewInt(int64(myRpt)))
	if err != nil {
		ac.err = err
		return
	}
}

// RegisterInProcHander registers the rpc.Server, handles RPC request to process the API requests in process
func (ac *AdmissionControl) RegisterInProcHander(localRcpServer *rpc.Server) {
	client := rpc.DialInProc(localRcpServer)
	ac.client = ethclient.NewClient(client)
}
