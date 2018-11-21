package backend

import (
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/types"
)

// BroadcastMinedBlock broadcasts generated block to committee
func (h *Handler) BroadcastMinedBlock(block *types.Block) {
	committee := h.signers
	log.Debug("broadcast new generated block to commttee", "number", block.NumberU64())
	for _, peer := range committee {
		peer.AsyncSendNewPendingBlock(block)
	}
}

// BroadcastPrepareSignedHeader broadcasts signed prepare header to remote committee
func (h *Handler) BroadcastPrepareSignedHeader(header *types.Header) {
	committee := h.signers
	for _, peer := range committee {
		peer.AsyncSendPrepareSignedHeader(header)
	}
}

// BroadcastCommitSignedHeader broadcasts signed commit header to remote committee
func (h *Handler) BroadcastCommitSignedHeader(header *types.Header) {
	committee := h.signers
	for _, peer := range committee {
		peer.AsyncSendCommitSignedHeader(header)
	}
}

// PendingBlockBroadcastLoop loops to broadcast blocks
func (h *Handler) PendingBlockBroadcastLoop() {
	futureTimer := time.NewTicker(10 * time.Second)
	defer futureTimer.Stop()

	for {
		select {
		case pendingBlock := <-h.pendingBlockCh:

			log.Debug("generated new pending block, broadcasting")

			done := false

			for !done {
				if h.Available() && len(h.signers) >= int(h.termLen) {
					// broadcast mined pending block to remote signers
					go h.BroadcastMinedBlock(pendingBlock)
					done = true
				}
			}

			// TODO: remove this
			// log.Debug("local block", "block", pendingBlock)

			// for i := 0; i < 100; i++ {
			// 	h.BroadcastMinedBlock(pendingBlock)
			// 	time.Sleep(3 * time.Second)
			// }

		// case <-futureTimer.C:

		// 	// check if still not received new block, if true, continue
		// 	if h.ReadyToImpeach() {

		// 		// get empty block
		// 		if emptyBlock, err := h.getEmptyBlockFn(); err == nil {

		// 			// broadcast the empty block
		// 			h.BroadcastGeneratedBlock(emptyBlock)
		// 		}
		// 	}

		case <-h.quitSync:
			return
		}
	}
}
