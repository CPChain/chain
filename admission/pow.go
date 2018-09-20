package admission

import (
	"time"

	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/core/types"
)

//pow base struct for pow.
type pow struct {
	//difficulty pow's difficulty.
	difficulty int64
	//address this node's address.
	address common.Address
	//blockHash the special block's hash.
	block *types.Block
	//lifeTime time limitation of pow.
	lifeTime time.Duration
	//nonce the number tries to find.
	nonce uint64
	// err unexpected err
	err error
}

//newPow returns struct pow.
func newPow(difficulty int64, address common.Address, block *types.Block, lifeTime time.Duration) *pow {
	return &pow{
		difficulty: difficulty,
		address:    address,
		block:      block,
		lifeTime:   lifeTime,
	}
}

func (p *pow) isOk() bool {
	return p.err == nil
}

func (p *pow) getError() error {
	return p.err
}
