package backend

import (
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/types"
)

// BroadcastMinedBlock broadcasts generated block to committee
func (h *Handler) BroadcastMinedBlock(block *types.Block) {
	h.lock.Lock()
	defer h.lock.Unlock()

	committee := h.signers
	log.Debug("broadcast new generated block to commttee", "number", block.NumberU64())
	for addr, peer := range committee {
		log.Debug("broadcast new generated block to commttee", "addr", addr.Hex())
		peer.AsyncSendNewPendingBlock(block)
	}
}

// BroadcastPrepareSignedHeader broadcasts signed prepare header to remote committee
func (h *Handler) BroadcastPrepareSignedHeader(header *types.Header) {
	h.lock.Lock()
	defer h.lock.Unlock()

	committee := h.signers
	for _, peer := range committee {
		peer.AsyncSendPrepareSignedHeader(header)
	}
}

// BroadcastCommitSignedHeader broadcasts signed commit header to remote committee
func (h *Handler) BroadcastCommitSignedHeader(header *types.Header) {
	h.lock.Lock()
	defer h.lock.Unlock()

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

			log.Debug("proposed new pending block, broadcasting")

			ready := false

			for !ready {
				if h.Available() && len(h.signers) >= int(h.termLen) {
					ready = true
				}
				time.Sleep(1 * time.Second)

				log.Debug("signer in dpor handler when broadcasting...")
				for addr := range h.signers {
					log.Debug("signer", "addr", addr.Hex())
				}
			}

			// broadcast mined pending block to remote signers
			go h.BroadcastMinedBlock(pendingBlock)

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
