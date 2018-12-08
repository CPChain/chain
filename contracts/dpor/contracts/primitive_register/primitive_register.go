package primitive_register

import (
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/apibackend_holder"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/primitives"
	"bitbucket.org/cpchain/chain/core/vm"
	"github.com/ethereum/go-ethereum/common"
)

type PrimitiveContractChecker struct {
	available bool
	lock      sync.RWMutex
}

var primitiveContractCheckerInstance *PrimitiveContractChecker
var once sync.Once

func GetPrimitiveContractCheckerInstance() *PrimitiveContractChecker {
	once.Do(func() {
		primitiveContractCheckerInstance = &PrimitiveContractChecker{}
	})
	return primitiveContractCheckerInstance
}

func (p *PrimitiveContractChecker) IsAvailable() bool {
	p.lock.RLock()
	defer p.lock.RUnlock()
	return p.available
}

func (p *PrimitiveContractChecker) SetAvailable(available bool) {
	p.lock.Lock()
	defer p.lock.Unlock()
	p.available = available
}

// TODO time is not for synchronization! REWRITE THIS @xumx
func (p *PrimitiveContractChecker) WaitInitCompleteUntilTimeout() {
	for i := 0; i < 10; i++ {
		if !p.IsAvailable() {
			time.Sleep(time.Duration(1) * time.Second)
		} else {
			log.Info("detect init Primitive Contract Complete")
			return
		}

	}
	log.Fatal("Init Primitive Contract Timeout,Exit")
}

type node interface {
	Service(service interface{}) error
	Attach() (*rpc.Client, error)
}

func RegisterPrimitiveContracts(n node) {
	rpcClient, err := n.Attach()
	if err != nil {
		log.Fatal("can't get rpc.client after start", "error", err)
	}
	client := cpclient.NewClient(rpcClient)
	contractClient := client
	chainClient := getChainClient(client)
	for addr, c := range MakePrimitiveContracts(contractClient, chainClient) {
		err = vm.RegisterPrimitiveContract(addr, c)
		if err != nil {
			log.Fatal("register primitive contract error", "error", err, "addr", addr)
		}
	}
	// change available to true
	GetPrimitiveContractCheckerInstance().SetAvailable(true)
}

func getChainClient(c *cpclient.Client) apibackend_holder.ChainApiClient {
	return apibackend_holder.ChainApiClient{ApiBackend: apibackend_holder.GetApiBackendHolderInstance().ApiBackend}
}

func MakePrimitiveContracts(contractClient backend.ContractBackend, chainClient apibackend_holder.ChainApiClient) map[common.Address]vm.PrimitiveContract {
	contracts := make(map[common.Address]vm.PrimitiveContract)

	// we start from 100 to reserve enough space for upstream primitive contracts.
	RptEvaluator, err := primitives.NewRptEvaluator(contractClient, chainClient)
	if err != nil {
		log.Fatal("s.RptEvaluator is file")
	}
	contracts[common.BytesToAddress([]byte{100})] = &primitives.GetRank{Backend: RptEvaluator}
	contracts[common.BytesToAddress([]byte{101})] = &primitives.GetMaintenance{Backend: RptEvaluator}
	contracts[common.BytesToAddress([]byte{102})] = &primitives.GetProxyCount{Backend: RptEvaluator}
	contracts[common.BytesToAddress([]byte{103})] = &primitives.GetUploadReward{Backend: RptEvaluator}
	contracts[common.BytesToAddress([]byte{104})] = &primitives.GetTxVolume{Backend: RptEvaluator}
	contracts[common.BytesToAddress([]byte{105})] = &primitives.IsProxy{Backend: RptEvaluator}
	contracts[common.BytesToAddress([]byte{106})] = &primitives.CpuPowValidate{}
	contracts[common.BytesToAddress([]byte{107})] = &primitives.MemPowValidate{}
	return contracts
}
