package admission

import (
	"bytes"
	"encoding/binary"
	"math/big"

	"github.com/ethereum/go-ethereum/common"
)

// validate tries the nonce.
func validate(difficulty uint64, headerBytes []byte, addr common.Address, nonce uint64, hashFn hashFn) bool {
	target := big.NewInt(1)
	target.Lsh(target, 256-uint(difficulty))

	nonceBytes := make([]byte, 8)
	binary.LittleEndian.PutUint64(nonceBytes, nonce)

	data := bytes.Join(
		[][]byte{
			addr.Bytes(),
			headerBytes,
			nonceBytes,
		}, nil)

	hash, _ := hashFn(data)
	return new(big.Int).SetBytes(hash[:]).Cmp(target) <= 0
}

func ValidateMemory(sender common.Address, blockHash []byte, nonce uint64, difficulty uint64) bool {
	return validate(difficulty, blockHash, sender, nonce, scryptFunc)
}

func ValidateCpu(sender common.Address, blockHash []byte, nonce uint64, difficulty uint64) bool {
	return validate(difficulty, blockHash, sender, nonce, sha256Func)
}
