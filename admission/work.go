package admission

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"math/big"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"golang.org/x/crypto/scrypt"
)

var (
	ErrPowAbort   = errors.New("proof work aborts")
	ErrPowTimeout = errors.New("proof work timeout")
)

type hashFn func([]byte) ([]byte, error)

func sha256Func(data []byte) ([]byte, error) {
	hash := sha256.Sum256(data)
	return hash[:], nil
}

func scryptFunc(data []byte) ([]byte, error) {
	return scrypt.Key(data, data[:8], 4096, 8, 1, 32)
}

type work struct {
	difficulty uint64
	nonce      uint64
	timeout    time.Duration
	coinbase   common.Address
	hashfn     hashFn
	header     *types.Header
	err        error
	mutex      sync.RWMutex
}

// newWork returns a new memoryWork instance
func newWork(difficulty uint64, timeout time.Duration, address common.Address, header *types.Header, hashfn hashFn) *work {
	return &work{
		difficulty: difficulty,
		timeout:    timeout,
		coinbase:   address,
		hashfn:     hashfn,
		header:     header,
	}
}

// result return the result
func (w *work) result() Result {
	w.mutex.RLock()
	defer w.mutex.RUnlock()

	return Result{
		BlockNumber: w.header.Number.Int64(),
		Nonce:       w.nonce,
	}
}

// error returns the work error
func (w *work) error() error {
	w.mutex.RLock()
	defer w.mutex.RUnlock()

	return w.err
}

// tryOnce tries the nonce.
func (w *work) tryOnce() bool {
	target := big.NewInt(1)
	target.Lsh(target, 256-uint(w.difficulty))

	data := w.makeData()
	hash, err := w.hashfn(data)
	if err != nil {
		w.mutex.Lock()
		w.err = err
		w.mutex.Unlock()
	}

	return new(big.Int).SetBytes(hash[:]).Cmp(target) <= 0
}

// makeData wrappers the nonce.
func (w *work) makeData() []byte {
	nonceBytes := make([]byte, 8)
	binary.LittleEndian.PutUint64(nonceBytes, w.nonce)

	return bytes.Join(
		[][]byte{
			w.coinbase.Bytes(),
			w.header.HashNoNonce().Bytes(),
			nonceBytes,
		},
		nil,
	)
}

// prove implements ProveBackend, generate the campaign information.
// starts cpu pow work.
func (w *work) prove(abort <-chan interface{}, wg *sync.WaitGroup) {
	defer wg.Done()
	start := time.Now()
	ticker := time.NewTicker(time.Duration(w.timeout))
	defer ticker.Stop()

search:
	for {
		select {
		case <-abort:
			w.mutex.Lock()
			w.err = ErrPowAbort
			w.mutex.Unlock()
			break search
		case <-ticker.C:
			w.mutex.Lock()
			w.err = ErrPowTimeout
			w.mutex.Unlock()
			break search
		default:
			w.mutex.RLock()
			nonce := w.nonce
			w.mutex.RUnlock()

			if nonce < maxNonce && validate(w.difficulty, w.header.Hash().Bytes(), w.coinbase, nonce, w.hashfn) {
				log.Info("found nonce", "block hash", w.header.Hash().Hex(), "difficulty", w.difficulty,
					"sender", w.coinbase.Hex(), "nonce", nonce, "timeCost(s)", time.Since(start).Seconds())
				break search
			}

			w.mutex.Lock()
			w.nonce++
			w.mutex.Unlock()
		}
	}
}
