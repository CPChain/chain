package admission

import (
	"errors"
	"math"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts"
	"github.com/ethereum/go-ethereum/common"
)

// Result is admission control examination result
type Result struct {
	BlockNumber int64  `json:"block_number"`
	Nonce       uint64 `json:"nonce"`
}

type workStatus = uint32

const (
	maxNonce = math.MaxUint64

	// AcIdle status done.
	AcIdle workStatus = iota + 1
	// AcRunning status running.
	AcRunning

	maxNumOfCampaignTerms = 10
	minNumOfCampaignTerms = 1
)

var (
	errTermOutOfRange = errors.New("the number of terms to campaign is out of range")
)

// AdmissionControl implements admission control functionality.
type AdmissionControl struct {
	config          Config
	address         common.Address
	chain           consensus.ChainReader
	key             *keystore.Key
	contractBackend contracts.Backend

	mutex      sync.RWMutex
	wg         *sync.WaitGroup
	cpuWork    ProofWork
	memoryWork ProofWork
	status     workStatus
	err        error
	abort      chan interface{}
	done       chan interface{}
}

// NewAdmissionControl returns a new Control instance.
func NewAdmissionControl(chain consensus.ChainReader, address common.Address, config Config) *AdmissionControl {
	return &AdmissionControl{
		config:  config,
		chain:   chain,
		address: address,
		status:  AcIdle,
	}
}

// Campaign starts running all the proof work to generate the campaign information and waits all proof work done, send msg
func (ac *AdmissionControl) Campaign(terms uint64) error {
	log.Info("Start campaign for dpor proposers committee")
	ac.mutex.Lock()
	defer ac.mutex.Unlock()

	if terms > maxNumOfCampaignTerms || terms < minNumOfCampaignTerms {
		return errTermOutOfRange
	}

	if ac.status == AcRunning {
		return nil
	}
	ac.status = AcRunning
	ac.err = nil
	ac.done = make(chan interface{})
	ac.abort = make(chan interface{})
	ac.buildWorks()
	ac.wg = new(sync.WaitGroup)
	ac.wg.Add(len(ac.getWorks()))
	for _, work := range ac.getWorks() {
		go work.prove(ac.abort, ac.wg)
	}

	go ac.waitSendCampaignMsg(terms)

	return nil
}

func (ac *AdmissionControl) DoneCh() <-chan interface{} {
	return ac.done
}

// Abort cancels all the proof work associated to the workType.
func (ac *AdmissionControl) Abort() {
	ac.mutex.Lock()
	defer ac.mutex.Unlock()

	if ac.status != AcRunning {
		return
	}

	// close channel to abort all work
	close(ac.abort)
	<-ac.done

	ac.abort = make(chan interface{})
	ac.status = AcIdle
}

// GetResult gets all work proofInfo
func (ac *AdmissionControl) GetResult() map[string]Result {
	ac.mutex.RLock()
	defer ac.mutex.RUnlock()

	results := make(map[string]Result)
	for name, work := range ac.getWorks() {
		results[name] = work.result()
	}
	return results
}

// SetAdmissionKey sets the key for admission control to participate campaign
func (ac *AdmissionControl) SetAdmissionKey(key *keystore.Key) {
	ac.mutex.Lock()
	defer ac.mutex.Unlock()

	ac.key = key
}

// GetStatus gets status of campaign
func (ac *AdmissionControl) GetStatus() (workStatus, error) {
	ac.mutex.RLock()
	defer ac.mutex.RUnlock()

	return ac.status, ac.err
}

// waitSendCampaignMsg waits all proof work done, then sends campaign proofInfo to campaign contract
func (ac *AdmissionControl) waitSendCampaignMsg(times uint64) {
	defer close(ac.done)
	ac.wg.Wait()

	defer func(ac *AdmissionControl) {
		ac.status = AcIdle
	}(ac)

	for _, work := range ac.getWorks() {
		// if work err then return
		if work.error() != nil {
			ac.err = work.error()
			return
		}
	}
	ac.sendCampaignResult(times)
}

// sendCampaignResult sends proof info to campaign contract
func (ac *AdmissionControl) sendCampaignResult(times uint64) {
	if ac.contractBackend == nil {
		ac.err = errors.New("contractBackend is nil")
		return
	}
	transactOpts := bind.NewKeyedTransactor(ac.key.PrivateKey)
	transactOpts.Value = new(big.Int).Mul(configs.Deposit(), new(big.Int).SetUint64(times))
	log.Info("transactOpts.Value", "value", transactOpts.Value)

	campaignContractAddress := configs.ChainConfigInfo().Dpor.Contracts[configs.ContractCampaign]
	log.Debug("CampaignContractAddress", "address", campaignContractAddress.Hex())
	instance, err := contracts.NewCampaignWrapper(transactOpts, campaignContractAddress, ac.contractBackend)
	if err != nil {
		ac.err = err
		return
	}

	cpuResult := ac.cpuWork.result()
	memResult := ac.memoryWork.result()
	_, err = instance.ClaimCampaign(new(big.Int).SetUint64(times), cpuResult.Nonce, new(big.Int).SetInt64(cpuResult.BlockNumber),
		memResult.Nonce, new(big.Int).SetInt64(memResult.BlockNumber))
	if err != nil {
		ac.err = err
		log.Warn("Error in claiming campaign", "error", err)
		return
	}
	log.Info("Claimed for campaign", "NumberOfCampaignTimes", times, "CpuPowResult", cpuResult.Nonce,
		"MemPowResult", memResult.Nonce, "CpuBlockNumber", cpuResult.BlockNumber, "MemBlockNumber", memResult.BlockNumber)
}

func (ac *AdmissionControl) setClientBackend(client *cpclient.Client) {
	ac.mutex.Lock()
	defer ac.mutex.Unlock()

	ac.contractBackend = client
}

// buildWorks creates proof works required by admission
func (ac *AdmissionControl) buildWorks() {
	ac.cpuWork = ac.buildCpuProofWork()
	ac.memoryWork = ac.buildMemoryProofWork()
}

func (ac *AdmissionControl) buildCpuProofWork() ProofWork {
	return newWork(ac.config.CpuDifficulty, ac.config.CpuLifeTime, ac.address, ac.chain.CurrentHeader(), sha256Func)
}

func (ac *AdmissionControl) buildMemoryProofWork() ProofWork {
	return newWork(ac.config.MemoryDifficulty, ac.config.MemoryCpuLifeTime, ac.address, ac.chain.CurrentHeader(), scryptFunc)
}

// registerProofWork returns all proof work
func (ac *AdmissionControl) getWorks() map[string]ProofWork {
	proofWorks := make(map[string]ProofWork)
	proofWorks[Cpu] = ac.cpuWork
	proofWorks[Memory] = ac.memoryWork
	return proofWorks
}
