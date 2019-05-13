package rpt

import (
	"context"
	"math/big"
	"sort"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	contracts "bitbucket.org/cpchain/chain/contracts/dpor/contracts/rpt"
	"github.com/ethereum/go-ethereum/common"
)

// RptCollectorImpl3 implements RptCollector
type RptCollectorImpl3 struct {
	rptInstance  *contracts.Rpt
	chainBackend backend.ChainBackend
	balances     *rptDataCache

	alpha int64
	beta  int64
	gamma int64
	psi   int64
	omega int64

	windowSize int

	currentNum uint64
	lock       sync.RWMutex
}

func NewRptCollectorImpl3(rptInstance *contracts.Rpt, chainBackend backend.ChainBackend) *RptCollectorImpl3 {

	return &RptCollectorImpl3{
		rptInstance:  rptInstance,
		chainBackend: chainBackend,
		balances:     newRptDataCache(),
		currentNum:   0,

		alpha: 50,
		beta:  15,
		gamma: 10,
		psi:   15,
		omega: 10,

		windowSize: 100,
	}
}

func (rc *RptCollectorImpl3) Alpha(num uint64) int64 {
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

func (rc *RptCollectorImpl3) Beta(num uint64) int64 {
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

func (rc *RptCollectorImpl3) Gamma(num uint64) int64 {
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

func (rc *RptCollectorImpl3) Psi(num uint64) int64 {
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

func (rc *RptCollectorImpl3) Omega(num uint64) int64 {
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

func (rc *RptCollectorImpl3) WindowSize(num uint64) int {
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

func (rc *RptCollectorImpl3) coefficients(num uint64) (int64, int64, int64, int64, int64) {
	return rc.Alpha(num), rc.Beta(num), rc.Gamma(num), rc.Psi(num), rc.Omega(num)
}

func (rc *RptCollectorImpl3) RptOf(addr common.Address, addrs []common.Address, num uint64) Rpt {

	windowSize := rc.WindowSize(num)
	alpha, beta, gamma, psi, omega := rc.coefficients(num)
	if num != rc.currentNum {
		rc.currentNum = num
	}

	rpt := int64(0)
	rpt = alpha*rc.RankValueOf(addr, addrs, num, windowSize) + beta*rc.TxsValueOf(addr, num, windowSize) + gamma*rc.MaintenanceValueOf(addr, num, windowSize) + psi*rc.UploadValueOf(addr, num, windowSize) + omega*rc.ProxyValueOf(addr, num, windowSize)

	if rpt <= minRptScore {
		rpt = minRptScore
	}
	return Rpt{Address: addr, Rpt: rpt}
}

func (rc *RptCollectorImpl3) RankValueOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {

	rank := rc.RankInfoOf(addr, addrs, num, windowSize)

	// some simple scoring
	if rank < 20 {
		return 20
	}
	if rank < 40 {
		return 40
	}
	if rank < 65 {
		return 60
	}
	if rank < 85 {
		return 70
	}
	if rank < 95 {
		return 80
	}
	if rank < 98 {
		return 90
	}
	return 100
}

func (rc *RptCollectorImpl3) TxsValueOf(addr common.Address, num uint64, windowSize int) int64 {
	count := rc.TxsInfoOf(addr, num, windowSize)

	if count > 100 {
		return 100
	}

	return count
}

func (rc *RptCollectorImpl3) MaintenanceValueOf(addr common.Address, num uint64, windowSize int) int64 {
	mtn := rc.MaintenanceInfoOf(addr, num, windowSize)
	if offset(num, windowSize) > 0 {
		if mtn <= 12 {
			return 60
		}

		if mtn < 24 {
			return 80
		}

		return 100
	}

	return 60
}

func (rc *RptCollectorImpl3) UploadValueOf(addr common.Address, num uint64, windowSize int) int64 {
	return rc.UploadInfoOf(addr, num, windowSize)
}

func (rc *RptCollectorImpl3) ProxyValueOf(addr common.Address, num uint64, windowSize int) int64 {
	return rc.ProxyInfoOf(addr, num, windowSize)
}

func (rc *RptCollectorImpl3) RankInfoOf(addr common.Address, addrs []common.Address, num uint64, windowSize int) int64 {
	tstart := time.Now()

	var rank int64
	// TODO: check this, why it is possible to be nil @liuq
	myBal, err := rc.chainBackend.BalanceAt(context.Background(), addr, big.NewInt(int64(num)))
	if myBal == nil || err != nil {
		return defaultRank
	}
	myBalance := myBal.Uint64()

	balances, ok := rc.balances.getCache(num)
	if !ok {
		for _, candidate := range addrs {
			balance, err := rc.chainBackend.BalanceAt(context.Background(), candidate, big.NewInt(int64(num)))
			if balance == nil || err != nil {
				return defaultRank
			}

			if candidate == addr {
				myBalance = balance.Uint64()
			}

			balances = append(balances, float64(balance.Uint64()))
		}
		sort.Sort(sort.Float64Slice(balances))
		rc.balances.addCache(num, balances)
	}

	// sort and get the rank
	index := sort.SearchFloat64s(balances, float64(myBalance))
	rank = int64(float64(index) / float64(len(addrs)) * 100)

	log.Debug("now calculating rpt", "Rank", "new", "num", num, "addr", addr.Hex(), "elapsed", common.PrettyDuration(time.Now().Sub(tstart)))
	return rank
}

func (rc *RptCollectorImpl3) TxsInfoOf(addr common.Address, num uint64, windowSize int) int64 {
	tstart := time.Now()
	txsCount := int64(0)

	nonce, err := rc.chainBackend.NonceAt(context.Background(), addr, big.NewInt(int64(num)))
	if err != nil {
		return txsCount
	}

	nonce0, err := rc.chainBackend.NonceAt(context.Background(), addr, big.NewInt(int64(offset(num, windowSize))))
	if err != nil {
		return txsCount
	}

	log.Debug("now calculating rpt", "Txs", "new", "num", num, "addr", addr.Hex(), "elapsed", common.PrettyDuration(time.Now().Sub(tstart)))
	return int64(nonce - nonce0)
}

func (rc *RptCollectorImpl3) MaintenanceInfoOf(addr common.Address, num uint64, windowSize int) int64 {
	tstart := time.Now()

	mtn := int64(0)
	for i := offset(num, windowSize); i < num; i++ {

		// TODO: check this, why it is possible to be nil @liuq
		header, err := rc.chainBackend.HeaderByNumber(context.Background(), big.NewInt(int64(i)))
		if header == nil || err != nil {
			continue
		}

		isProposer := header.Coinbase == addr
		if isProposer {
			mtn += 2
			continue
		}

		inProposers := false
		for _, ad := range header.Dpor.Proposers {
			if addr == ad {
				inProposers = true
				break
			}
		}
		if inProposers {
			mtn += 1
			continue
		}

		mtn += 0
	}

	log.Debug("now calculating rpt", "Maintenance", "new", "num", num, "addr", addr.Hex(), "elapsed", common.PrettyDuration(time.Now().Sub(tstart)))
	return mtn
}

func (rc *RptCollectorImpl3) UploadInfoOf(addr common.Address, num uint64, windowSize int) int64 {
	log.Debug("now calculating rpt", "UploadInfo", "new", "num", num, "addr", addr.Hex())

	return 0
}

func (rc *RptCollectorImpl3) ProxyInfoOf(addr common.Address, num uint64, windowSize int) int64 {
	log.Debug("now calculating rpt", "ProxyInfo", "new", "num", num, "addr", addr.Hex())

	return 0
}
