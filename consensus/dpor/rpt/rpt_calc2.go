package rpt

import (
	"context"
	"math/big"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	contracts "bitbucket.org/cpchain/chain/contracts/dpor/rpt"
	"github.com/ethereum/go-ethereum/common"
)

const (
	impeachPunishmentWindowSize = 10000
	maxAllowedImpeachedBlocks   = 9
)

// CollectorImpl2 implements RptCollector
type CollectorImpl2 struct {
	rptInstance  *contracts.Rpt
	chainBackend backend.ChainBackend
	balances     *rptDataCache
	txs          *rptDataCache
	mtns         *rptDataCache

	impeachHistory impeachHistory

	alpha int64
	beta  int64
	gamma int64
	psi   int64
	omega int64

	windowSize int

	currentNum uint64
	lock       sync.RWMutex
}

// NewCollectorImpl2 creates an CollectorImpl2
func NewCollectorImpl2(rptInstance *contracts.Rpt, chainBackend backend.ChainBackend) *CollectorImpl2 {

	return &CollectorImpl2{
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
func (rc *CollectorImpl2) Alpha(num uint64) int64 {
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
func (rc *CollectorImpl2) Beta(num uint64) int64 {
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
func (rc *CollectorImpl2) Gamma(num uint64) int64 {
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
func (rc *CollectorImpl2) Psi(num uint64) int64 {
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
func (rc *CollectorImpl2) Omega(num uint64) int64 {
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
func (rc *CollectorImpl2) WindowSize(num uint64) int {
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

func (rc *CollectorImpl2) coefficients(num uint64) (int64, int64, int64, int64, int64) {
	return rc.Alpha(num), rc.Beta(num), rc.Gamma(num), rc.Psi(num), rc.Omega(num)
}

// RptOf returns the reputation value of a given address among a batch addresses
func (rc *CollectorImpl2) RptOf(addr common.Address, addrs []common.Address, num uint64) Rpt {

	windowSize := rc.WindowSize(num)
	alpha, beta, gamma, psi, omega := rc.coefficients(num)
	if num != rc.currentNum {
		rc.currentNum = num
	}

	rpt := int64(0)
	punishment := rc.ImpeachPunishment(addr, addrs, num)
	rpt = alpha*rc.BalanceValueOf(addr, addrs, num, windowSize) +
		beta*rc.TxsValueOf(addr, addrs, num, windowSize) +
		gamma*rc.MaintenanceValueOf(addr, addrs, num, windowSize) +
		psi*rc.UploadValueOf(addr, addrs, num, windowSize) +
		omega*rc.ProxyValueOf(addr, addrs, num, windowSize)

	// decrease the rpt value according to the impeach history
	rpt = int64(float32(rpt) * punishment)

	if rpt < defaultMinimumRptValue {
		rpt = defaultMinimumRptValue
	}

	return Rpt{Address: addr, Rpt: rpt}
}

func impeachPunishRatio(impeachedNumber int) float32 {
	if impeachedNumber <= 0 {
		return 1
	}

	if impeachedNumber > maxAllowedImpeachedBlocks {
		return 0
	}

	return 1. - float32(impeachedNumber)/maxAllowedImpeachedBlocks
}

// ImpeachPunishment returns the decline ratio according to the impeachment history of the rnode.
// the returned values are in [0., 1/n, 2/n, ..., (n-1)/n, 1] where n equals to `maxAllowedImpeachedBlocks`.
func (rc *CollectorImpl2) ImpeachPunishment(addr common.Address, addrs []common.Address, num uint64) float32 {
	rc.lock.Lock()
	defer rc.lock.Unlock()

	// if the impeachHistory is nil, then it must be at initialization state, create an instance
	if rc.impeachHistory == nil {
		rc.impeachHistory = newImpeachHistoryImpl(num, rc.chainBackend)
	}

	// rpt is calculated periodically, so it is needed to update all of those impeach status
	// from last update time on.
	rc.impeachHistory.addHistories(rc.impeachHistory.currentNumber(), num, rc.chainBackend)

	// now that impeach history is already updated, count the impeached blocks from the outset on
	count := rc.impeachHistory.countHistory(addr)
	punishment := impeachPunishRatio(count)

	log.Debug("punishment", "p", punishment, "addr", addr.Hex(), "num", num, "count", count)
	return punishment
}

// BalanceValueOf returns Balance Value of reputation
func (rc *CollectorImpl2) BalanceValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	rank := rc.BalanceInfoOf(addr, addrs, num, windowSize)
	return rank
}

// TxsValueOf returns Transaction Count of reputation
func (rc *CollectorImpl2) TxsValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	rank := rc.TxsInfoOf(addr, addrs, num, windowSize)
	return rank
}

// MaintenanceValueOf returns Chain Maintenance of reputation
func (rc *CollectorImpl2) MaintenanceValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	rank := rc.MaintenanceInfoOf(addr, addrs, num, windowSize)
	return rank
}

// UploadValueOf returns File Contribution of reputation
func (rc *CollectorImpl2) UploadValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	rank := rc.UploadInfoOf(addr, addrs, num, windowSize)
	return rank
}

// ProxyValueOf returns Proxy Information of PDash of reputation
func (rc *CollectorImpl2) ProxyValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	rank := rc.ProxyInfoOf(addr, addrs, num, windowSize)
	return rank
}

// BalanceInfoOf minor
func (rc *CollectorImpl2) BalanceInfoOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
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
	key := newRptDataCacheKey(num, addrs)
	balances, ok := rc.balances.getCache(key)
	if !ok {
		for _, candidate := range addrs {
			balance := getBalance(candidate, num)
			balances = append(balances, float64(balance))
		}
		balances = sortAndReverse(balances)
		rc.balances.addCache(key, balances)
	}

	// sort and get the rank
	rank = getRank(float64(myBalance), balances)

	log.Debug("now calculating rpt", "Balance", "new", "num", num, "addr", addr.Hex(), "elapsed", common.PrettyDuration(time.Now().Sub(start)))
	return rank
}

// TxsInfoOf minor
func (rc *CollectorImpl2) TxsInfoOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
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
	key := newRptDataCacheKey(num, addrs)
	txs, ok := rc.txs.getCache(key)
	if !ok {
		for _, candidate := range addrs {
			txC := getTxCount(candidate, num)
			txs = append(txs, float64(txC))
		}
		txs = sortAndReverse(txs)
		rc.txs.addCache(key, txs)
	}

	// sort and get the rank
	rank = getRank(float64(txsCount), txs)

	log.Debug("now calculating rpt", "Txs", "new", "num", num, "addr", addr.Hex(), "elapsed", common.PrettyDuration(time.Now().Sub(start)))
	return rank
}

// MaintenanceInfoOf minor
func (rc *CollectorImpl2) MaintenanceInfoOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
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
	key := newRptDataCacheKey(num, addrs)
	mtns, ok := rc.mtns.getCache(key)
	if !ok {
		for _, candidate := range addrs {
			mtnI := getMtn(candidate, num)
			mtns = append(mtns, float64(mtnI))
		}
		mtns = sortAndReverse(mtns)
		rc.mtns.addCache(key, mtns)
	}

	// sort and get the rank
	rank = getRank(float64(myMtn), mtns)

	log.Debug("now calculating rpt", "Maintenance", "new", "num", num, "addr", addr.Hex(), "elapsed", common.PrettyDuration(time.Now().Sub(start)))
	return rank
}

// UploadInfoOf minor
func (rc *CollectorImpl2) UploadInfoOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	log.Debug("now calculating rpt", "UploadInfo", "new", "num", num, "addr", addr.Hex())
	return 0
}

// ProxyInfoOf minor
func (rc *CollectorImpl2) ProxyInfoOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	log.Debug("now calculating rpt", "ProxyInfo", "new", "num", num, "addr", addr.Hex())
	return 0
}
