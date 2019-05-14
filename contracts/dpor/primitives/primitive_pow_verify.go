package primitives

import (
	"math/big"

	"bitbucket.org/cpchain/chain/admission"
	"bitbucket.org/cpchain/chain/configs"
	"github.com/ethereum/go-ethereum/common"
)

var (
	// true32Byte is returned if the bn256 pairing check succeeds.
	true32Byte = []byte{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1}

	// false32Byte is returned if the bn256 pairing check fails.
	false32Byte = make([]byte, 32)
)

// MemPowValidate implements a memory nonce validate
type MemPowValidate struct{}

// RequiredGas returns the gas required to execute the pre-compiled contract.
func (m *MemPowValidate) RequiredGas(input []byte) uint64 {
	return configs.MemPowValidateGas
}

func (m *MemPowValidate) Run(input []byte) ([]byte, error) {
	address, nonce, blockHash, difficulty := unpackPowValidateArgs(input)
	if admission.ValidateMemory(address, blockHash, nonce, difficulty) {
		return true32Byte, nil
	} else {
		return false32Byte, nil
	}
}

// CpuPowValidate does a cpu POW proof validation.
type CpuPowValidate struct{}

func (m *CpuPowValidate) RequiredGas(input []byte) uint64 {
	return configs.CpuPowValidateGas
}

func (m *CpuPowValidate) Run(input []byte) ([]byte, error) {
	address, nonce, blockHash, difficulty := unpackPowValidateArgs(input)
	if admission.ValidateCpu(address, blockHash, nonce, difficulty) {
		return true32Byte, nil
	} else {
		return false32Byte, nil
	}
}

func unpackPowValidateArgs(input []byte) (address common.Address, nonce uint64, blockHash []byte, difficulty uint64) {
	address = common.BytesToAddress(input[12:32])
	nonce = new(big.Int).SetBytes(input[32:64]).Uint64()
	blockHash = input[64:96]
	difficulty = new(big.Int).SetBytes(input[96:128]).Uint64()
	return
}
