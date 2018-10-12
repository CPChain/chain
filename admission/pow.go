package admission

import (
	"time"

	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// pow base struct for pow.
type pow struct {
	// difficulty pow's difficulty.
	difficulty int64
	// address this node's address.
	address common.Address
	// header the header used for POW
	header *types.Header
	// lifeTime time limitation of pow.
	lifeTime time.Duration
	// nonce the number tries to find.
	nonce uint64
	// err unexpected err
	err error
}

// newPow returns struct pow.
func newPow(difficulty int64, lifeTime time.Duration, address common.Address, header *types.Header) *pow {
	return &pow{
		difficulty: difficulty,
		address:    address,
		header:     header,
		lifeTime:   lifeTime,
	}
}

func (p *pow) isOk() bool {
	return p.err == nil
}

func (p *pow) getError() error {
	return p.err
}
