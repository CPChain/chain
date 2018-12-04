package backend

import (
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/types"
)

// BroadcastPreprepareBlock broadcasts generated block to committee
func (h *Handler) BroadcastPreprepareBlock(block *types.Block) {

	log.Debug("proposed new pending block, broadcasting")

	ready := false
	term := h.dpor.TermOf(block.NumberU64())

	// wait until there is enough validators
	for !ready {
		time.Sleep(1 * time.Second)

		validators := h.dialer.ValidatorsOfTerm(term)

		log.Debug("signer in dpor handler when broadcasting...")
		for addr := range validators {
			log.Debug("signer", "addr", addr.Hex())
		}

		if len(validators) >= int(h.config.TermLen) {
			ready = true
		}
	}

	log.Debug("broadcast new generated block to commttee", "number", block.NumberU64())

	committee := h.dialer.ValidatorsOfTerm(term)
	for addr, peer := range committee {
		log.Debug("broadcast new generated block to commttee", "addr", addr.Hex())
		peer.AsyncSendPreprepareBlock(block)
	}
}

// BroadcastPreprepareImpeachBlock broadcasts generated impeach block to committee
func (h *Handler) BroadcastPreprepareImpeachBlock(block *types.Block) {

	log.Debug("proposed new pending block, broadcasting")

	ready := false
	term := h.dpor.TermOf(block.NumberU64())

	// wait until there is enough validators
	for !ready {
		time.Sleep(1 * time.Second)

		validators := h.dialer.ValidatorsOfTerm(term)

		log.Debug("signer in dpor handler when broadcasting...")
		for addr := range validators {
			log.Debug("signer", "addr", addr.Hex())
		}

		if len(validators) >= int(h.config.TermLen) {
			ready = true
		}
	}

	log.Debug("broadcast new generated block to commttee", "number", block.NumberU64())

	committee := h.dialer.ValidatorsOfTerm(term)
	for addr, peer := range committee {
		log.Debug("broadcast new generated block to commttee", "addr", addr.Hex())
		peer.AsyncSendPreprepareImpeachBlock(block)
	}
}

// BroadcastPrepareHeader broadcasts signed prepare header to remote committee
func (h *Handler) BroadcastPrepareHeader(header *types.Header) {
	h.lock.Lock()
	defer h.lock.Unlock()

	term := h.dpor.TermOf(header.Number.Uint64())
	committee := h.dialer.ValidatorsOfTerm(term)

	for _, peer := range committee {
		peer.AsyncSendPrepareHeader(header)
	}
}

// BroadcastPrepareImpeachHeader broadcasts signed impeach prepare header to remote committee
func (h *Handler) BroadcastPrepareImpeachHeader(header *types.Header) {
	h.lock.Lock()
	defer h.lock.Unlock()

	term := h.dpor.TermOf(header.Number.Uint64())
	committee := h.dialer.ValidatorsOfTerm(term)

	for _, peer := range committee {
		peer.AsyncSendPrepareImpeachHeader(header)
	}
}

// BroadcastCommitHeader broadcasts signed commit header to remote committee
func (h *Handler) BroadcastCommitHeader(header *types.Header) {
	h.lock.Lock()
	defer h.lock.Unlock()

	term := h.dpor.TermOf(header.Number.Uint64())
	committee := h.dialer.ValidatorsOfTerm(term)

	for _, peer := range committee {
		peer.AsyncSendCommitHeader(header)
	}
}

// BroadcastCommitImpeachHeader broadcasts signed impeach commit header to remote committee
func (h *Handler) BroadcastCommitImpeachHeader(header *types.Header) {
	h.lock.Lock()
	defer h.lock.Unlock()

	term := h.dpor.TermOf(header.Number.Uint64())
	committee := h.dialer.ValidatorsOfTerm(term)

	for _, peer := range committee {
		peer.AsyncSendCommitImpeachHeader(header)
	}
}

// PendingBlockBroadcastLoop loops to broadcast blocks
func (h *Handler) PendingBlockBroadcastLoop() {
	futureTimer := time.NewTicker(time.Duration(h.dpor.ImpeachTimeout()))
	defer futureTimer.Stop()

	for {
		select {
		case pendingBlock := <-h.pendingBlockCh:

			// broadcast mined pending block to remote signers
			go h.BroadcastPreprepareBlock(pendingBlock)

		case <-futureTimer.C:

			// check if still not received new block, if true, continue
			if h.ReadyToImpeach() {
				// get empty block

				impeachHeader, act, dtype, msg, err := h.fsm.Fsm(nil, 0, ImpeachPreprepareMsgCode)

				if impeachHeader != nil && act == BroadcastMsgAction && dtype == HeaderType && msg == PrepareMsgCode && err == nil {
					header := impeachHeader.(*types.Header)
					go h.BroadcastPrepareImpeachHeader(header)
				}

			}

		case <-h.quitSync:
			return
		}
	}
}
