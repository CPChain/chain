package backend

import "bitbucket.org/cpchain/chain/types"

// ReceiveMinedPendingBlock receives a block to add to pending block channel
func (vh *Handler) ReceiveMinedPendingBlock(block *types.Block) error {
	select {
	case vh.pendingBlockCh <- block:
		err := vh.knownBlocks.AddBlock(block)
		if err != nil {
			return err
		}

		return nil
	}
}
