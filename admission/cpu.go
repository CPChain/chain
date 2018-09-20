package admission

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"math/big"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/core/types"
)

// cpuWork cpu proof work
type cpuWork struct {
	*pow
}

// newCPUWork returns a new instance of cpuWork
func newCPUWork(difficulty int64, address common.Address, block *types.Block, lifeTime time.Duration) *cpuWork {
	return &cpuWork{
		pow: newPow(difficulty, address, block, lifeTime),
	}
}

//tryOnce tries the nonce.
func (cpu *cpuWork) tryOnce() bool {
	target := big.NewInt(1)
	target.Lsh(target, 256-uint(cpu.difficulty))

	var hash [32]byte
	data := cpu.makeData()

	hash = sha256.Sum256(data)

	return new(big.Int).SetBytes(hash[:]).Cmp(target) <= 0
}

//makeData wrappers the nonce.
func (cpu *cpuWork) makeData() []byte {
	nonceBytes := make([]byte, 8)
	binary.LittleEndian.PutUint64(nonceBytes, cpu.nonce)

	return bytes.Join(
		[][]byte{
			cpu.address.Bytes(),
			cpu.block.Hash().Bytes(),
			nonceBytes,
		},
		nil,
	)
}

// prove implements ProveBackend, generate the campaign information.
// starts cpu pow work.
func (cpu *cpuWork) prove(abort chan struct{}, wg *sync.WaitGroup) {
	defer wg.Done()
	ticker := time.NewTicker(cpu.lifeTime)
	defer ticker.Stop()

search:
	for {
		select {
		case <-abort:
			cpu.err = errors.New("proof work aborts")
			break search
		case <-ticker.C:
			close(abort)
			cpu.err = errors.New("proof work timeout")
			break search
		default:
			if cpu.nonce < maxNonce && cpu.tryOnce() {
				break search
			}
			cpu.nonce++
		}
	}
}

// getProofInfo return the cpu pow result
func (cpu *cpuWork) getProofInfo() interface{} {
	return CPUProofInfo{
		Nonce:       cpu.nonce,
		BlockNumber: cpu.block.NumberU64(),
	}
}
