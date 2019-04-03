package backend

import (
	"bitbucket.org/cpchain/chain/types"
)

// ReceiveMinedPendingBlock receives a block to add to pending block channel
func (ph *Handler) ReceiveMinedPendingBlock(block *types.Block) error {
	select {
	case ph.pendingBlockCh <- block:
		err := ph.knownBlocks.AddBlock(block)
		if err != nil {
			return err
		}

		return nil
	}
}
