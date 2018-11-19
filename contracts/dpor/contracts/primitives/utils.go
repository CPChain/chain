package primitives

import (
	"errors"
	"math/big"

	"github.com/ethereum/go-ethereum/common"
)

var (
	errWrongInput = errors.New("input's length must be 64 bytes")
)

// extractRptPrimitivesArgs extracts arguments from input byte slice
func extractRptPrimitivesArgs(input []byte) (common.Address, uint64, error) {
	if len(input) != 64 {
		return common.Address{}, 0, errWrongInput
	}

	return common.BytesToAddress(input[12:32]), new(big.Int).SetBytes(input[32:64]).Uint64(), nil
}
