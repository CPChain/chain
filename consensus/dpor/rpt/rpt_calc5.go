package rpt

import (
	"context"
	"math/big"
	"sort"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	contracts "bitbucket.org/cpchain/chain/contracts/dpor/rpt"
	"github.com/ethereum/go-ethereum/common"
)

// RptCollectorImpl5 implements RptCollector
type RptCollectorImpl5 struct {
	rptInstance  *contracts.Rpt
	chainBackend backend.ChainBackend
	balances     *rptDataCache
	txs          *rptDataCache
	mtns         *rptDataCache

	alpha int64
	beta  int64
	gamma int64
	psi   int64
	omega int64

	windowSize int

	currentNum uint64
	lock       sync.RWMutex
}

// NewRptCollectorImpl5 creates an RptCollectorImpl5
func NewRptCollectorImpl5(rptInstance *contracts.Rpt, chainBackend backend.ChainBackend) *RptCollectorImpl5 {

	return &RptCollectorImpl5{
		rptInstance:  rptInstance,
		chainBackend: chainBackend,
		balances:     newRptDataCache(),
		txs:          newRptDataCache(),
		mtns:         newRptDataCache(),
		currentNum:   0,

		alpha: 50,
		beta:  15,
		gamma: 10,
		psi:   15,
		omega: 10,

		windowSize: 100,
	}
}

// Alpha returns the coefficient of balance(coin age)
func (rc *RptCollectorImpl5) Alpha(num uint64) int64 {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	if rc.rptInstance == nil || num == rc.currentNum {
		return rc.alpha
	}

	a, err := rc.rptInstance.Alpha(nil)
	if err == nil {
		log.Debug("using parameters from contract", "alpha", a.Int64(), "num", num)
		rc.alpha = a.Int64()
	}

	return rc.alpha
}

// Beta returns the coefficient of transaction count
func (rc *RptCollectorImpl5) Beta(num uint64) int64 {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	if rc.rptInstance == nil || num == rc.currentNum {
		return rc.beta
	}

	b, err := rc.rptInstance.Beta(nil)
	if err == nil {
		log.Debug("using parameters from contract", "beta", b.Int64(), "num", num)
		rc.beta = b.Int64()
	}

	return rc.beta
}

// Gamma returns the coefficient of Maintenance
func (rc *RptCollectorImpl5) Gamma(num uint64) int64 {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	if rc.rptInstance == nil || num == rc.currentNum {
		return rc.gamma
	}

	g, err := rc.rptInstance.Gamma(nil)
	if err == nil {
		log.Debug("using parameters from contract", "gamma", g.Int64(), "num", num)
		rc.gamma = g.Int64()
	}

	return rc.gamma
}

// Psi returns the coefficient of File Contribution
func (rc *RptCollectorImpl5) Psi(num uint64) int64 {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	if rc.rptInstance == nil || num == rc.currentNum {
		return rc.psi
	}

	p, err := rc.rptInstance.Psi(nil)
	if err == nil {
		log.Debug("using parameters from contract", "psi", p.Int64(), "num", num)
		rc.psi = p.Int64()
	}

	return rc.psi
}

// Omega returns the coefficient of Proxy Information in Pdash
func (rc *RptCollectorImpl5) Omega(num uint64) int64 {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	if rc.rptInstance == nil || num == rc.currentNum {
		return rc.omega
	}

	o, err := rc.rptInstance.Omega(nil)
	if err == nil {
		log.Debug("using parameters from contract", "omega", o.Int64(), "num", num)
		rc.omega = o.Int64()
	}

	return rc.omega
}

// WindowSize returns the windown size when calculating reputation value
func (rc *RptCollectorImpl5) WindowSize(num uint64) int {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	if rc.rptInstance == nil || num == rc.currentNum {
		return rc.windowSize
	}

	w, err := rc.rptInstance.Window(nil)
	if err == nil {
		log.Debug("using parameters from contract", "window", w.Int64(), "num", num)
		rc.windowSize = int(w.Int64())
	}

	return rc.windowSize
}

func (rc *RptCollectorImpl5) coefficients(num uint64) (int64, int64, int64, int64, int64) {
	return rc.Alpha(num), rc.Beta(num), rc.Gamma(num), rc.Psi(num), rc.Omega(num)
}

// RptOf returns the reputation value of a given address among a batch addresses
func (rc *RptCollectorImpl5) RptOf(addr common.Address, addrs []common.Address, num uint64) Rpt {

	windowSize := rc.WindowSize(num)
	alpha, beta, gamma, psi, omega := rc.coefficients(num)
	if num != rc.currentNum {
		rc.currentNum = num
	}

	rpt := int64(0)
	rpt = alpha*rc.BalanceValueOf(addr, addrs, num, windowSize) + beta*rc.TxsValueOf(addr, addrs, num, windowSize) + gamma*rc.MaintenanceValueOf(addr, addrs, num, windowSize) + psi*rc.UploadValueOf(addr, addrs, num, windowSize) + omega*rc.ProxyValueOf(addr, addrs, num, windowSize)

	if rpt <= minRptScore {
		rpt = minRptScore
	}
	return Rpt{Address: addr, Rpt: rpt}
}

// BalanceValueOf returns Balance Value of reputation
func (rc *RptCollectorImpl5) BalanceValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	rank := rc.BalanceInfoOf(addr, addrs, num, windowSize)
	return rank
}

// TxsValueOf returns Transaction Count of reputation
func (rc *RptCollectorImpl5) TxsValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	rank := rc.TxsInfoOf(addr, addrs, num, windowSize)
	return rank
}

// MaintenanceValueOf returns Chain Maintenance of reputation
func (rc *RptCollectorImpl5) MaintenanceValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	rank := rc.MaintenanceInfoOf(addr, addrs, num, windowSize)
	return rank
}

// UploadValueOf returns File Contribution of reputation
func (rc *RptCollectorImpl5) UploadValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	rank := rc.UploadInfoOf(addr, addrs, num, windowSize)
	return rank
}

// ProxyValueOf returns Proxy Information of PDash of reputation
func (rc *RptCollectorImpl5) ProxyValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	rank := rc.ProxyInfoOf(addr, addrs, num, windowSize)
	return rank
}

// BalanceInfoOf minor
func (rc *RptCollectorImpl5) BalanceInfoOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	start := time.Now()

	getBalance := func(address common.Address, number uint64) uint64 {
		balance, err := rc.chainBackend.BalanceAt(context.Background(), address, big.NewInt(int64(number)))
		if balance == nil || err != nil {
			return 0
		}
		return new(big.Int).Div(balance, big.NewInt(configs.Cpc)).Uint64()
	}

	var rank int64
	myBalance := getBalance(addr, num)
	balances, ok := rc.balances.getCache(num)
	if !ok {
		for _, candidate := range addrs {
			balance := getBalance(candidate, num)
			balances = append(balances, float64(balance))
		}
		balances = sortAndReverse(balances)
		rc.balances.addCache(num, balances)
	}

	// sort and get the rank
	rank = getRank(float64(myBalance), balances)

	log.Debug("now calculating rpt", "Balance", "new", "num", num, "addr", addr.Hex(), "elapsed", common.PrettyDuration(time.Now().Sub(start)))
	return rank
}

// TxsInfoOf minor
func (rc *RptCollectorImpl5) TxsInfoOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	start := time.Now()

	getTxCount := func(address common.Address, number uint64) int64 {
		txsCount := int64(0)
		nonce, err := rc.chainBackend.NonceAt(context.Background(), address, big.NewInt(int64(number)))
		if err != nil {
			return txsCount
		}

		nonce0, err := rc.chainBackend.NonceAt(context.Background(), address, big.NewInt(int64(offset(number, windowSize))))
		if err != nil {
			return txsCount
		}

		txsCount = int64(nonce - nonce0)
		return txsCount
	}

	var rank int64
	txsCount := getTxCount(addr, num)
	txs, ok := rc.txs.getCache(num)
	if !ok {
		for _, candidate := range addrs {
			txC := getTxCount(candidate, num)
			txs = append(txs, float64(txC))
		}
		txs = sortAndReverse(txs)
		rc.txs.addCache(num, txs)
	}

	// sort and get the rank
	rank = getRank(float64(txsCount), txs)

	log.Debug("now calculating rpt", "Txs", "new", "num", num, "addr", addr.Hex(), "elapsed", common.PrettyDuration(time.Now().Sub(start)))
	return rank
}

// MaintenanceInfoOf minor
func (rc *RptCollectorImpl5) MaintenanceInfoOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	start := time.Now()

	getMtn := func(addr common.Address, num uint64) int64 {
		mtn := int64(0)
		for i := offset(num, windowSize); i < num; i++ {
			header, err := rc.chainBackend.HeaderByNumber(context.Background(), big.NewInt(int64(i)))
			if header == nil || err != nil {
				continue
			}

			isProposer := header.Coinbase == addr
			if isProposer {
				mtn++
			}
		}
		return mtn
	}

	var rank int64
	myMtn := getMtn(addr, num)
	mtns, ok := rc.mtns.getCache(num)
	if !ok {
		for _, candidate := range addrs {
			mtnI := getMtn(candidate, num)
			mtns = append(mtns, float64(mtnI))
		}
		mtns = sortAndReverse(mtns)
		rc.mtns.addCache(num, mtns)
	}

	// sort and get the rank
	rank = getRank(float64(myMtn), mtns)

	log.Debug("now calculating rpt", "Maintenance", "new", "num", num, "addr", addr.Hex(), "elapsed", common.PrettyDuration(time.Now().Sub(start)))
	return rank
}

// UploadInfoOf minor
func (rc *RptCollectorImpl5) UploadInfoOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	log.Debug("now calculating rpt", "UploadInfo", "new", "num", num, "addr", addr.Hex())
	return 1
}

// ProxyInfoOf minor
func (rc *RptCollectorImpl5) ProxyInfoOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	log.Debug("now calculating rpt", "ProxyInfo", "new", "num", num, "addr", addr.Hex())
	return 1
}

// getRank return the rank of the given item among the array
// the array is in decreasing order
func getRank(item float64, array sort.Float64Slice) int64 {
	len := len(array)
	index := searchIndex(item, array)
	rank := int64((1 - float64(index)/float64(len)) * 100)
	log.Debug("array", "array", array, "rank", rank, "index", index, "len", len)
	return rank
}

// sortAndReverse returns an decreasing order of the given array
func sortAndReverse(array []float64) sort.Float64Slice {
	sort.Sort(sort.Reverse(sort.Float64Slice(array)))
	return array
}

// searchIndex return the index of an item in an array
func searchIndex(item float64, array []float64) int64 {
	for i, x := range array {
		if x == item {
			return int64(i)
		}
	}
	return int64(len(array))
}
