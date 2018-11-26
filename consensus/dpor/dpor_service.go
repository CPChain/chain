package dpor

import (
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// VerifyRemoteValidator validates if a given address is signer of current epoch
func (d *Dpor) VerifyRemoteValidator(signer common.Address) (bool, error) {

	// TODO: fix this
	return true, nil
}

// VerifyHeaderWithState verifies the given header
// if in preprepared state, verify basic fields
// if in prepared state, verify if enough prepare sigs
// if in committed state, verify if enough commit sigs
func (d *Dpor) VerifyHeaderWithState(header *types.Header, state consensus.State) error {

	// TODO: fix this, !!! state
	return d.VerifyHeader(d.chain, header, true, header)
}

// ValidateBlock validates a basic field excepts seal of a block.
func (d *Dpor) ValidateBlock(block *types.Block) error {
	return d.dh.validateBlock(d, d.chain, block)
}

// SignHeader signs the header and adds all known sigs to header
func (d *Dpor) SignHeader(header *types.Header, state consensus.State) error {

	// TODO: fix this, !!! state
	switch err := d.dh.signHeader(d, d.chain, header, state); err {
	case nil:
		return nil
	default:
		return consensus.ErrWhenSigningHeader
	}
}

// BroadcastBlock broadcasts a block to normal peers(not pbft replicas)
func (d *Dpor) BroadcastBlock(block *types.Block, prop bool) {
	go d.pmBroadcastBlockFn(block, prop)
}

// InsertChain inserts a block to chain
func (d *Dpor) InsertChain(block *types.Block) error {
	_, err := d.chain.InsertChain(types.Blocks{block})
	return err
}

// Status returns a pbft replica's status
func (d *Dpor) Status() *consensus.PbftStatus {
	return d.PbftStatus()
}

// StatusUpdate updates status of dpor
func (d *Dpor) StatusUpdate() error {

	// TODO: fix this
	return nil
}

// GetEmptyBlock returns an empty block for view change
func (d *Dpor) GetEmptyBlock() (*types.Block, error) {
	// TODO: fix this
	return nil, nil
}

// HasBlockInChain returns if a block is in local chain
func (d *Dpor) HasBlockInChain(hash common.Hash, number uint64) bool {
	blk := d.chain.GetBlock(hash, number)
	if blk != nil {
		return true
	}
	return false
}
