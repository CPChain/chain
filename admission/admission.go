package admission

import (
	"context"
	"errors"
	"math"
	"math/big"
	"net"
	"reflect"
	"sync"
	"sync/atomic"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/contracts/dpor/admission"
	campaign "bitbucket.org/cpchain/chain/contracts/dpor/campaign"
	contracts "bitbucket.org/cpchain/chain/contracts/dpor/campaign/tests"
	"bitbucket.org/cpchain/chain/contracts/dpor/network"
	rnode "bitbucket.org/cpchain/chain/contracts/dpor/rnode"
	"github.com/ethereum/go-ethereum/common"
)

// Result is admission control examination result
type Result struct {
	BlockNumber int64  `json:"block_number"`
	Nonce       uint64 `json:"nonce"`
	Success     bool   `json:"success"`
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

	Cpu    = "cpu"
	Memory = "memory"
)

var (
	errTermOutOfRange = errors.New("the number of terms to campaign is out of range")
	errNotRNode       = errors.New("it is not RNode, not able to participate campaign")
	errLockedPeriod   = errors.New("the period is locked, cannot invest now")
	errNoEnoughMoney  = errors.New("money is not enough to become RNode")
	errBadNetwork     = errors.New("now the network status is bad")
)

// AdmissionControl implements admission control functionality.
type AdmissionControl struct {
	address               common.Address
	chain                 consensus.ChainReader
	key                   *keystore.Key
	contractBackend       contracts.Backend
	admissionContractAddr common.Address
	campaignContractAddr  common.Address
	rNodeContractAddr     common.Address
	networkContractAddr   common.Address

	checkNetworkStatus bool

	mutex      sync.RWMutex
	wg         *sync.WaitGroup
	cpuWork    ProofWork
	memoryWork ProofWork
	status     workStatus
	err        error
	abort      chan interface{}
	done       chan interface{}

	sendingFund int32
}

// TODO: implement Authorize like consensus.Engine @liuq

// NewAdmissionControl returns a new Control instance.
func NewAdmissionControl(chain consensus.ChainReader, address common.Address, admissionContractAddr common.Address,
	campaignContractAddr common.Address, rNodeContractAddr common.Address, networkContractAddr common.Address) *AdmissionControl {
	return &AdmissionControl{
		chain:                 chain,
		address:               address,
		admissionContractAddr: admissionContractAddr,
		campaignContractAddr:  campaignContractAddr,
		rNodeContractAddr:     rNodeContractAddr,
		networkContractAddr:   networkContractAddr,
		status:                AcIdle,

		checkNetworkStatus: true,
	}
}

func (ac *AdmissionControl) IgnoreNetworkCheck() {
	ac.mutex.Lock()
	defer ac.mutex.Unlock()

	ac.checkNetworkStatus = false
}

func (ac *AdmissionControl) CheckNetworkStatus() bool {
	ac.mutex.RLock()
	localCheck := ac.checkNetworkStatus
	ac.mutex.RUnlock()

	// TODO: read parameters from contract
	host := "www.microsoft.com:443"
	count := 4
	timeout := 300
	check := true
	gap := 100

	// create contract instance
	networkCheckerInstance, err := network.NewNetwork(ac.networkContractAddr, ac.contractBackend)
	if err != nil {
		log.Error("failed to create new network checker instance", "err", err)
		return false
	}

	chck, err := networkCheckerInstance.Open(nil)
	if err != nil {
		log.Error("failed to get dial open flag from network checker instance", "err", err)
		return false
	}
	check = chck

	// if check flag is false, return true
	if !check || !localCheck {
		return true
	}

	// read parameters from contract
	host, err = networkCheckerInstance.Host(nil)
	if err != nil {
		log.Error("failed to get host from network checker instance", "err", err)
		return false
	}

	cnt, err := networkCheckerInstance.Count(nil)
	if err != nil {
		log.Error("failed to get dial count from network checker instance", "err", err)
		return false
	}

	count = int(cnt.Uint64())

	tmout, err := networkCheckerInstance.Timeout(nil)
	if err != nil {
		log.Error("failed to get dial count from network checker instance", "err", err)
		return false
	}
	timeout = int(tmout.Uint64())

	gp, err := networkCheckerInstance.Gap(nil)
	if err != nil {
		log.Error("failed to get dial gap from network checker instance", "err", err)
		return false
	}
	gap = int(gp.Uint64())

	// do the dial
	if ok, err := checkNetworkStatus(host, count, timeout, gap); !ok {
		log.Warn("Failed to check network status, try to dial", "host", host, "count", count, "timeout", timeout, "gap", gap, "err", err)
		return false
	}

	return true
}

func checkNetworkStatus(host string, count int, timeout int, gap int) (bool, error) {

	timeoutD := time.Duration(time.Duration(timeout) * time.Millisecond)
	gapD := time.Duration(time.Duration(gap) * time.Millisecond)

	for i := 0; i < count; i++ {
		conn, err := net.DialTimeout("tcp", host, timeoutD)
		if err != nil {
			return false, err
		}
		log.Debug("dialed host to check network status", "host", host, "count", count, "timeout", timeout, "gap", gap)
		conn.Close()
		time.Sleep(gapD)
	}
	return true, nil
}

// Campaign starts running all the proof work to generate the campaign information and waits all proof work done, send msg
func (ac *AdmissionControl) Campaign(terms uint64) error {

	// check network status before continue, this is not a hard restriction
	// one can ignore this by setting `IgnoreNetworkStatusCheck' == true in configs/general.go
	if !ac.CheckNetworkStatus() {
		return errBadNetwork
	}

	log.Info("Start campaign for dpor proposers committee")
	ac.mutex.Lock()
	defer ac.mutex.Unlock()

	if terms > maxNumOfCampaignTerms || terms < minNumOfCampaignTerms {
		return errTermOutOfRange
	}

	if ac.status == AcRunning {
		return nil
	}

	isRNode, _ := ac.IsRNode()
	if !isRNode {
		return errNotRNode
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

// IsRNode returns true or false indicating whether the node is RNode which is able to participate campaign
func (ac *AdmissionControl) IsRNode() (bool, error) {
	rNodeContractAddress := ac.rNodeContractAddr
	log.Debug("RNodeContractAddress", "address", rNodeContractAddress.Hex())
	rNodeContract, err := rnode.NewRnode(rNodeContractAddress, ac.contractBackend)
	if err != nil {
		return false, err
	}

	isRNode, _ := rNodeContract.IsRnode(nil, ac.address)
	return isRNode, nil
}

func (ac *AdmissionControl) FundForRNode() error {

	// check network status before continue, this is not a hard restriction
	// one can ignore this by setting `IgnoreNetworkStatusCheck' == true in configs/general.go
	if !ac.CheckNetworkStatus() {
		return errBadNetwork
	}

	log.Debug("Start funding for becoming RNode")
	ac.mutex.Lock()
	defer ac.mutex.Unlock()

	sending := atomic.LoadInt32(&ac.sendingFund)
	if sending != 0 {
		return nil // there is a pending tx to fund for becoming RNode, wait for its accomplishment
	}

	rNodeContractAddress := ac.rNodeContractAddr
	log.Debug("RNodeContractAddress", "address", rNodeContractAddress.Hex())
	rNodeContract, err := rnode.NewRnode(rNodeContractAddress, ac.contractBackend)
	if err != nil {
		return err
	}

	isRNode, err := rNodeContract.IsRnode(nil, ac.address)
	if err != nil {
		return err
	}

	if isRNode {
		// already RNode, no more action needed
		return nil
	}

	minRnodeFund, err := rNodeContract.RnodeThreshold(nil)
	if err != nil {
		return err
	}

	balance, _ := ac.contractBackend.BalanceAt(context.Background(), ac.address, nil)
	if balance.Cmp(minRnodeFund) >= 0 {
		transactOpts := bind.NewKeyedTransactor(ac.key.PrivateKey)
		transactOpts.Value = minRnodeFund
		tx, err := rNodeContract.JoinRnode(
			transactOpts,
			new(big.Int).SetInt64(configs.RnodeVersion),
		)
		if err != nil {
			log.Info("encounter error when funding deposit for node to become candidate", "error", err)
			return err
		}

		atomic.StoreInt32(&ac.sendingFund, 1)
		go ac.waitForTxDone(tx.Hash())

		log.Info("save fund for the node to become RNode", "account", ac.address, "txhash", tx.Hash().Hex())
		return nil
	} else {
		log.Info("not enough money to become RNode")
		return errNoEnoughMoney
	}
}

func (ac *AdmissionControl) waitForTxDone(txhash common.Hash) {
	defer func() {
		atomic.StoreInt32(&ac.sendingFund, 0)
	}()

	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	for {
		select {
		case <-ctx.Done():
			log.Warn("transaction is not processed in time", "txhash", txhash.Hex())
			return
		default:
			r, err := ac.contractBackend.TransactionReceipt(context.Background(), txhash)
			if r != nil && err == nil {
				log.Debug("TransactionReceipt Status", "txhash", txhash.Hex(), "Status", r.Status)
				return
			}

			time.Sleep(500 * time.Millisecond)
		}
	}
}

func (ac *AdmissionControl) DoneCh() <-chan interface{} {
	return ac.done
}

// Abort cancels all the proof work associated to the workType.
func (ac *AdmissionControl) Abort() {
	ac.mutex.RLock()
	status := ac.status
	ac.mutex.RUnlock()
	if status != AcRunning {
		return
	}

	// close channel to abort all work
	close(ac.abort)
	<-ac.done

	ac.mutex.Lock()
	defer ac.mutex.Unlock()
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
func (ac *AdmissionControl) waitSendCampaignMsg(terms uint64) {
	defer close(ac.done)
	ac.wg.Wait()

	defer func(ac *AdmissionControl) {
		ac.mutex.Lock()
		ac.status = AcIdle
		ac.mutex.Unlock()
	}(ac)

	ac.mutex.RLock()
	works := ac.getWorks()
	ac.mutex.RUnlock()

	for _, work := range works {
		// if work err then return
		if work.error() != nil {
			ac.mutex.Lock()
			ac.err = work.error()
			ac.mutex.Unlock()
			log.Info("work is not pass ac", "error is", work.error())
			return
		}
	}
	go ac.sendCampaignResult(terms)
}

// sendCampaignResult sends proof info to campaign contract
func (ac *AdmissionControl) sendCampaignResult(terms uint64) {
	if ac.contractBackend == nil || reflect.TypeOf(ac.contractBackend).String() == "*backends.SimulatedBackend" {
		ac.mutex.Lock()
		ac.err = errors.New("contractBackend is nil")
		ac.mutex.Unlock()
		return
	}

	transactOpts := bind.NewKeyedTransactor(ac.key.PrivateKey)
	// this is an *empirical* estimate of the possible largest gas needed by the claimCampaign smartcontract call.
	// @liusw for this number.
	transactOpts.GasLimit = 2300000

	campaignContractAddress := ac.campaignContractAddr
	log.Debug("CampaignContractAddress", "address", campaignContractAddress.Hex())
	instance, err := campaign.NewCampaign(campaignContractAddress, ac.contractBackend)
	if err != nil {
		ac.mutex.Lock()
		ac.err = err
		ac.mutex.Unlock()
		return
	}

	cpuResult := ac.cpuWork.result()
	memResult := ac.memoryWork.result()

	log.Info("ready to claim campaign",
		"terms", terms,
		"cpu result", cpuResult.Nonce,
		"cpu number", cpuResult.BlockNumber,
		"mem result", memResult.Nonce,
		"mem number", memResult.BlockNumber,
		"campaign version", configs.CampaignVersion,
		"gas limit", transactOpts.GasLimit,
	)

	_, err = instance.ClaimCampaign(
		transactOpts,
		new(big.Int).SetUint64(terms),
		cpuResult.Nonce,
		new(big.Int).SetInt64(cpuResult.BlockNumber),
		memResult.Nonce,
		new(big.Int).SetInt64(memResult.BlockNumber),
		new(big.Int).SetInt64(configs.CampaignVersion),
	)
	if err != nil {
		ac.mutex.Lock()
		ac.err = err
		ac.mutex.Unlock()
		log.Warn("Error in claiming campaign", "error", err)
		return
	}
	log.Info("Claimed for campaign", "NumberOfCampaignTerms", terms, "CpuPowResult", cpuResult.Nonce,
		"MemPowResult", memResult.Nonce, "CpuBlockNumber", cpuResult.BlockNumber, "MemBlockNumber", memResult.BlockNumber)
}

func (ac *AdmissionControl) setClientBackend(client *cpclient.Client) {
	ac.mutex.Lock()
	defer ac.mutex.Unlock()

	ac.contractBackend = client
}

func (ac *AdmissionControl) SetSimulateBackend(contractBackend contracts.Backend) {
	ac.mutex.Lock()
	defer ac.mutex.Unlock()

	ac.contractBackend = contractBackend
}

// buildWorks creates proof works required by admission
func (ac *AdmissionControl) buildWorks() {
	ac.cpuWork = ac.buildCpuProofWork()
	ac.memoryWork = ac.buildMemoryProofWork()
}

func (ac *AdmissionControl) buildCpuProofWork() ProofWork {
	client := ac.contractBackend
	instance, err := admission.NewAdmission(ac.admissionContractAddr, client)
	if err != nil {
		log.Fatal("NewAdmissionCaller is error", "error is", err)
	}
	cd, _, clt, _, err := instance.GetAdmissionParameters(nil)
	if err != nil {
		log.Fatal("GetAdmissionParameters is error", "error is ", err)
	}
	cpuDifficulty := cd.Uint64()
	cpuLifeTime := time.Duration(time.Duration(clt.Int64()) * time.Second)

	// must use current block number - 1, because solidity cannot get hash of current block
	blockNum := ac.chain.CurrentHeader().Number.Uint64()
	if blockNum > 0 {
		blockNum = blockNum - 1
	}
	return newWork(cpuDifficulty, cpuLifeTime, ac.address, ac.chain.GetHeaderByNumber(blockNum), sha256Func)
}

func (ac *AdmissionControl) buildMemoryProofWork() ProofWork {
	client := ac.contractBackend
	instance, err := admission.NewAdmission(ac.admissionContractAddr, client)
	if err != nil {
		log.Fatal("NewAdmissionCaller is error", "error is", err)
	}
	_, md, _, mct, err := instance.GetAdmissionParameters(nil)
	if err != nil {
		log.Fatal("GetDifficultyParameter is error", "error is", err)
	}
	memoryDifficulty := md.Uint64()
	memoryCpuLifeTime := time.Duration(time.Duration(mct.Int64()) * time.Second)

	// must use current block number - 1, because solidity cannot get hash of current block
	blockNum := ac.chain.CurrentHeader().Number.Uint64()
	if blockNum > 0 {
		blockNum = blockNum - 1
	}
	return newWork(memoryDifficulty, memoryCpuLifeTime, ac.address, ac.chain.GetHeaderByNumber(blockNum), scryptFunc)
}

// registerProofWork returns all proof work
func (ac *AdmissionControl) getWorks() map[string]ProofWork {
	proofWorks := make(map[string]ProofWork)
	proofWorks[Cpu] = ac.cpuWork
	proofWorks[Memory] = ac.memoryWork
	return proofWorks
}
