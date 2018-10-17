package rpt

// this package collects all reputation calculation related information,
// then calculates the reputations of candidates.

import (
	"context"
	"fmt"
	"math/big"
	"sort"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/ethclient"
	"bitbucket.org/cpchain/chain/rpc"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/log"
	"bitbucket.org/cpchain/chain/consensus"

)

var (
	extraVanity = 32 // Fixed number of extra-data prefix bytes reserved for signer vanity
	extraSeal   = 65 // Fixed number of extra-data suffix bytes reserved for signer seal
)

// RPT defines the name and reputation pair.
type RPT struct {
	Address common.Address
	Rpt     float64
}

// RPTs is an array of RPT.
type RPTs []RPT

// This is used for sorting.
func (a RPTs) Len() int           { return len(a) }
func (a RPTs) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a RPTs) Less(i, j int) bool { return a[i].Rpt < a[j].Rpt }

// Collector collects all rpt related information from block txs and contracts.
type Collector interface {
	GetRpts(addresses []common.Address, number uint64) RPTs

	GetRptInfo(address common.Address, number uint64) Info
	GetRptInfos(addresses common.Address, number uint64) map[common.Address]Info

	calcRptInfo(address common.Address, number uint64) RPT

	getChainRptInfo(address common.Address, number uint64) ChainRptInfo
	getContractRptInfo(address common.Address, number uint64) ContractRptInfo
}

// CollectorConfig is the config of rpt info collector
type CollectorConfig struct {
	LeaderReward    float64
	ProxyReward     float64
	UploadReward    float64
	CommitteReward  float64
	Alpha           float64 // coinAge coefficient
	Beta            float64 // dataUpload coefficient
	Gamma           float64 // proxyReward coefficient
	Phi             float64 // leaderReward coefficient
	Omega           float64 // txVolume coefficient
	WindowSize      uint64  // window size, how many blocks to recall.
	Chain           consensus.ChainReader
	Committeadress  []common.Address
	ChainConfig     *configs.ChainConfig
	DporConfig      *configs.DporConfig
	campaignAddress common.Address
	//	rptAddress common.Address
	client       *ethclient.Client
	rnodeaddress []common.Address
	//	view_idx *big.Int
	committeenamber int
}

// ClientBackend is the client operation interface
type ClientBackend interface {
	BalanceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (*big.Int, error)
	BlockByNumber(ctx context.Context, number *big.Int) (*types.Block, error)
	HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error)
}

// BasicCollector is the default rpt collector
type BasicCollector struct {
	// TODO: backend here.
	//*ethclient.Client
	ClientBackend
	Config CollectorConfig
}

// ChainRptInfo is the rpt info from chain
type ChainRptInfo struct {
	CoinAge  float64
	TxVolume float64
	IfLeader float64
}

// ContractRptInfo is the rpt info from contracts.
type ContractRptInfo struct {
	ProxyReward  float64
	UploadReward float64
}

// Info is the whole rpt info.
type Info struct {
	Number       uint64
	ChainInfo    ChainRptInfo
	ContractInfo ContractRptInfo
}

func NewEthClient(endpoint string) (*ethclient.Client, error) {
	log.Info("connecting to RPT API", "url", endpoint)
	client, err := rpc.Dial(endpoint)
	if err != nil {
		return nil, err
	}
	return ethclient.NewClient(client), nil

}

// NewBasicCollector returns a new BasicCollector object.
func NewBasicCollector(ethClient ClientBackend, config *CollectorConfig) (*BasicCollector, error) {
	bc := &BasicCollector{
		ClientBackend: ethClient,
		Config:        *config,
	}
	return bc, nil
}

// GetRpts returns reputation of the given addresses.
func (bc *BasicCollector) GetRpts(addresses []common.Address, number uint64) RPTs {
	rpts := RPTs{}
	for i := 0; i < len(addresses); i++ {
		rpts = append(rpts, bc.calcRptInfo((addresses)[i],addresses, number))
	}
	return rpts
}


// GetRptInfos returns reputation info of given address.
func (bc *BasicCollector) GetRptInfos(addresses []common.Address, number uint64) map[common.Address]Info {
	infos := make(map[common.Address]Info)
	for _, address := range addresses {
		infos[address] = Info{
			ChainInfo: bc.getChainRptInfo(address,addresses, number),
			ContractInfo: bc.getContractRptInfo(address, number),
		}
	}
	return infos
}

func (bc *BasicCollector) calcRptInfo(address common.Address,addresses []common.Address, number uint64) RPT {
	rpt := 0.0
	alpha, beta, gamma, phi, omega := bc.Config.Alpha, bc.Config.Beta, bc.Config.Gamma, bc.Config.Phi, bc.Config.Omega
	for i := number; i >= 0; i-- {
		chainInfo := bc.getChainRptInfo(address,addresses, i)
		contractInfo := bc.getContractRptInfo(address, i)
		fmt.Println(chainInfo.CoinAge, chainInfo.TxVolume, chainInfo.IfLeader, contractInfo.UploadReward, contractInfo.ProxyReward)
		rptInfo := alpha*chainInfo.CoinAge + beta*chainInfo.TxVolume + gamma*chainInfo.IfLeader + phi*contractInfo.UploadReward + omega*contractInfo.ProxyReward
		rpt += rptInfo
		if i <= number-bc.Config.WindowSize {
			break
		}
	}
	return RPT{Address: address, Rpt: rpt}
}

func (bc *BasicCollector) getChainRptInfo(address common.Address,addresses []common.Address, number uint64) ChainRptInfo {
	//coinAge, txVolume, ifLeader := 0., 0., 0.
	ca, err := bc.getCoinAge(address,addresses, number)
	if err != nil {
		log.Warn("getCoinAge error", address, err)
		return ChainRptInfo{
			CoinAge:  0,
			TxVolume: 0,
			IfLeader: 0,
		}
	}
	tv, err := bc.getTxVolume(address, number)
	if err != nil {
		log.Warn("getTxVolume error", address, err)
		return ChainRptInfo{
			CoinAge:  0,
			TxVolume: 0,
			IfLeader: 0,
		}
	}
	Mr, err := bc.getMaintenance(address, number)
	if err != nil {
		log.Warn("getIfLeader error", address, err)
		return ChainRptInfo{
			CoinAge:  0,
			TxVolume: 0,
			IfLeader: 0,
		}
	}
	return ChainRptInfo{
		CoinAge:  ca,
		TxVolume: tv,
		IfLeader: Mr,
	}
}

func (bc *BasicCollector) getContractRptInfo(address common.Address, number uint64) ContractRptInfo {
	uploadReward, proxyReward := 0., 0.
	if number == 0 {
		uploadReward += bc.getUploadReward(address, 0)
		proxyReward += bc.getProxyReward(address, 0)
	} else {
		uploadReward += bc.getUploadReward(address, number)
		proxyReward += bc.getProxyReward(address, number)
	}
	return ContractRptInfo{
		UploadReward: uploadReward,
		ProxyReward:  proxyReward,
	}
}

func (bc *BasicCollector) getCoinAge(address common.Address,addresses []common.Address, number uint64) (float64, error) {
	var balances []float64
	mybalance, err := bc.BalanceAt(context.Background(), address, big.NewInt(int64(number)))
	if err != nil {
			log.Warn("error with bc.getReputationnode", "error", err)
			}
	for _, committee := range addresses {
		balance, err := bc.BalanceAt(context.Background(), committee, big.NewInt(int64(number)))
		if err != nil {
			log.Warn("error with bc.BalanceAt", "error", err)
			return 0, err
		}
		balances = append(balances, float64(balance.Uint64()))
	}
	var rank float64
	sort.Sort(sort.Reverse(sort.Float64Slice(balances)))
		index := sort.SearchFloat64s(balances, float64(mybalance.Uint64()))
		rank = float64(index / bc.Config.committeenamber)
		switch {
		case rank <= 0.02:
			return 100.0, err
		case rank <= 0.05:
			return 90.0, err
		case rank <= 0.15:
			return 80, err
		case rank <= 0.35:
			return 70, err
		case rank <= 0.6:
			return 60, err
		case rank <= 0.8:
			return 40, err
		default:
			return 20, err

		}
	}

func (bc *BasicCollector) getTxVolume(address common.Address, number uint64) (float64, error) {
	block, err := bc.BlockByNumber(context.Background(), big.NewInt(int64(number)))
	if err != nil {
		log.Warn("error with bc.getTxVolume", "error", err)
		return 0, err
	}
	txvs := float64(0)
	signer := types.NewPrivTxSupportEIP155Signer(bc.Config.ChainConfig.ChainID)
	txs := block.Transactions()
		for _, tx := range txs {
			sender, err := signer.Sender(tx)
			if err != nil {
				continue
			}
			if sender == address {
				//		txvs += float64(tx.Value().Uint64())
				txvs += 5
			}
			if txvs == 100 {
				break
			}
		}
	return txvs, nil
}

func (bc *BasicCollector) getIfLeader(address common.Address, number uint64) (float64, error) {
	if bc.Config.ChainConfig.ChainID.Uint64() == uint64(4) {
		return 0, nil
	}
	header, err := bc.HeaderByNumber(context.Background(), big.NewInt(int64(number)))
	if err != nil {
		log.Warn("error with bc.getIfLeader", "error", err)
		return 0, err
	}
	number = number%bc.Config.DporConfig.Epoch - 1
	leaderBytes := header.Extra[uint64(extraVanity)+number*common.AddressLength : uint64(extraVanity)+(number+1)*common.AddressLength]
	leader := common.BytesToAddress(leaderBytes)

	fmt.Println("leader.Hex():", leader.Hex())

	if leader == address {
		return bc.Config.LeaderReward, err
	}
	return 0, err
}

func (bc *BasicCollector) getMaintenance(address common.Address, number uint64) (float64, error) {
	ld, cm := 0.0, 0.0
	if bc.Config.ChainConfig.ChainID.Uint64() == uint64(4) {
		return 0, nil
	}
	header, err := bc.HeaderByNumber(context.Background(), big.NewInt(int64(number)))
	if err != nil {
		log.Warn("error with bc.getIfLeader", "error", err)
		return 0, err
	}
	number = number%bc.Config.DporConfig.Epoch - 1
	leaderBytes := header.Extra[uint64(extraVanity)+number*common.AddressLength : uint64(extraVanity)+(number+1)*common.AddressLength]
	leader := common.BytesToAddress(leaderBytes)

	fmt.Println("leader.Hex():", leader.Hex())

		if leader == address {
			ld = bc.Config.LeaderReward - bc.Config.CommitteReward
		}
		for _, committe := range bc.getcommiteetmember(bc.Config.Chain,number) {
			if address == committe {
				cm = bc.Config.CommitteReward
				return ld+cm, nil
			}
		}
	return 60, nil
}

func (bc *BasicCollector) getUploadReward(address common.Address, number uint64) float64 {
	// TODO: implement this.
	upload := bc.getuploadRecord(number)
	for _,uploadaddress := range upload{
		if uploadaddress==address{
			return bc.Config.UploadReward
		}
	}
	return 0
}

func (bc *BasicCollector) getProxyReward(address common.Address, number uint64) float64 {
	// TODO: implement this need abi of contract
	ProxyReward := 0.0
	var proxyaddresses []common.Address
	orderId := bc.getorderRecords(number)
	for orderid := range orderId {
		proxyaddresses = append(proxyaddresses, OrderMap[orderid].ProxyAddress)
	}
	for _, proxyaddress := range proxyaddresses {
		if proxyaddress == address {
			ProxyReward += 10
			break
		}
	}
	for orderid := range orderId {
		if OrderMap[orderid].ProxyAddress == address {
			if OrderMap[orderid].State.Finished == true {
				ProxyReward += 5
			}
		}
		if ProxyReward == 100 {
			break
		}
	}
	return ProxyReward
	//    return  bc.Config.ProxyReward
}

//func (bc *BasicCollector)getReputationnode(view_idx *big.Int)([]common.Address, error){
//	instance, err:= contract.NewCampaign(bc.Config.campaignAddress, bc.Config.client)
//	if err != nil{
//		log.Warn("NewCampaign error", bc.Config.campaignAddress, err)
//	}
//	Reputationnode,err:= instance.CandidatesOf(nil,view_idx)
//	if err != nil {
//		log.Warn("Reputationnode error", bc.Config.campaignAddress, err)
//	}
//	copy(bc.Config.rnodeaddress,Reputationnode)
//	return Reputationnode,err
//}

func (bc *BasicCollector) getorderRecords(number uint64) []int {
	//todo :xuejie
	OrderRecords := []int{1, 2, 3, 4, 5}
	return OrderRecords
}

func (bc *BasicCollector)getuploadRecord(number uint64) []common.Address {
	var uploadadress  []common.Address
	return uploadadress
}
func (bc *BasicCollector)getcommiteetmember(chain consensus.ChainReader,number uint64 )[]common.Address  {
	genesis := chain.GetHeaderByNumber(number)
	committee := make([]common.Address, (len(genesis.Extra)-extraVanity-extraSeal)/common.AddressLength)
	for i := 0; i < len(committee); i++ {
		copy(committee[i][:], genesis.Extra[extraVanity+i*common.AddressLength:extraVanity+(i+1)*common.AddressLength])
	}
    return committee
}