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
	return Result{
		BlockNumber: w.header.Number.Int64(),
		Nonce:       w.nonce,
	}
}

// error returns the work error
func (w *work) error() error {
	return w.err
}

// tryOnce tries the nonce.
func (w *work) tryOnce() bool {
	target := big.NewInt(1)
	target.Lsh(target, 256-uint(w.difficulty))

	data := w.makeData()
	hash, err := w.hashfn(data)
	if err != nil {
		w.err = err
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
func (w *work) prove(abort chan interface{}, wg *sync.WaitGroup) {
	defer wg.Done()
	ticker := time.NewTicker(time.Duration(w.timeout))
	defer ticker.Stop()

search:
	for {
		select {
		case <-abort:
			w.err = errors.New("proof work aborts")
			break search
		case <-ticker.C:
			close(abort)
			w.err = errors.New("proof work timeout")
			break search
		default:
			if w.nonce < maxNonce && validate(w.difficulty, w.header.Hash().Bytes(), w.coinbase, w.nonce, w.hashfn) {
				log.Info("found nonce", "block hash", w.header.Hash().Bytes(), "difficulty", w.difficulty, "sender", w.coinbase.Hex(), "nonce", w.nonce)
				break search
			}
			w.nonce++
		}
	}
}
