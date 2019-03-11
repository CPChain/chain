package backend

import (
	"math/rand"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/rlp"
)

func waitForEnoughValidator(h *Handler, term uint64, quitCh chan struct{}) (validators map[common.Address]*RemoteValidator) {
	for {
		select {
		case <-quitCh:
			return

		default:

			validators = h.dialer.ValidatorsOfTerm(term)

			if len(validators) >= int(h.dpor.ValidatorsNum()-h.fsm.Faulty())-1 {
				return
			}

			time.Sleep(time.Duration(rand.Intn(5)) * time.Second)
		}
	}
}

// BroadcastPreprepareBlock broadcasts generated block to validators
func (h *Handler) BroadcastPreprepareBlock(block *types.Block) {

	log.Debug("proposed new pending block, broadcasting")

	term := h.dpor.TermOf(block.NumberU64())
	validators := waitForEnoughValidator(h, term, h.quitCh)

	for _, peer := range validators {
		peer.AsyncSendPreprepareBlock(block)
	}
}

// BroadcastPreprepareImpeachBlock broadcasts generated impeach block to validators
func (h *Handler) BroadcastPreprepareImpeachBlock(block *types.Block) {

	log.Debug("proposed new pending impeach block, broadcasting")

	term := h.dpor.TermOf(block.NumberU64())
	validators := waitForEnoughValidator(h, term, h.quitCh)

	for _, peer := range validators {
		peer.AsyncSendPreprepareImpeachBlock(block)
	}
}

// BroadcastPrepareHeader broadcasts signed prepare header to remote validators
func (h *Handler) BroadcastPrepareHeader(header *types.Header) {
	h.lock.Lock()
	defer h.lock.Unlock()

	log.Debug("composed prepare header msg, broadcasting", "number", header.Number.Uint64())

	term := h.dpor.TermOf(header.Number.Uint64())
	validators := waitForEnoughValidator(h, term, h.quitCh)

	for _, peer := range validators {
		peer.AsyncSendPrepareHeader(header)
	}
}

// BroadcastPrepareImpeachHeader broadcasts signed impeach prepare header to remote validators
func (h *Handler) BroadcastPrepareImpeachHeader(header *types.Header) {
	h.lock.Lock()
	defer h.lock.Unlock()

	log.Debug("composed prepare impeach header msg, broadcasting", "number", header.Number.Uint64())

	term := h.dpor.TermOf(header.Number.Uint64())
	validators := waitForEnoughValidator(h, term, h.quitCh)

	for _, peer := range validators {
		peer.AsyncSendPrepareImpeachHeader(header)
	}
}

// BroadcastCommitHeader broadcasts signed commit header to remote validators
func (h *Handler) BroadcastCommitHeader(header *types.Header) {
	h.lock.Lock()
	defer h.lock.Unlock()

	log.Debug("composed commit header msg, broadcasting", "number", header.Number.Uint64())

	term := h.dpor.TermOf(header.Number.Uint64())
	validators := waitForEnoughValidator(h, term, h.quitCh)

	for _, peer := range validators {
		peer.AsyncSendCommitHeader(header)
	}
}

// BroadcastCommitImpeachHeader broadcasts signed impeach commit header to remote validators
func (h *Handler) BroadcastCommitImpeachHeader(header *types.Header) {
	h.lock.Lock()
	defer h.lock.Unlock()

	log.Debug("composed commit impeach header msg, broadcasting", "number", header.Number.Uint64())

	term := h.dpor.TermOf(header.Number.Uint64())
	validators := waitForEnoughValidator(h, term, h.quitCh)

	for _, peer := range validators {
		peer.AsyncSendCommitImpeachHeader(header)
	}
}

// BroadcastValidateBlock broadcasts validate block to validators
func (h *Handler) BroadcastValidateBlock(block *types.Block) {

	log.Debug("composed validate block, broadcasting")

	term := h.dpor.TermOf(block.NumberU64())
	validators := waitForEnoughValidator(h, term, h.quitCh)

	for _, peer := range validators {
		peer.AsyncSendValidateBlock(block)
	}
}

// BroadcastValidateImpeachBlock broadcasts validate impeach block to validators
func (h *Handler) BroadcastValidateImpeachBlock(block *types.Block) {

	log.Debug("composed validate impeach block, broadcasting")

	term := h.dpor.TermOf(block.NumberU64())
	validators := waitForEnoughValidator(h, term, h.quitCh)

	for _, peer := range validators {
		peer.AsyncSendImpeachValidateBlock(block)
	}
}

// PendingBlockBroadcastLoop loops to broadcast blocks
func (h *Handler) PendingBlockBroadcastLoop() {

	for {
		select {
		case pendingBlock := <-h.pendingBlockCh:
			// broadcast mined pending block to remote signers
			go h.BroadcastPreprepareBlock(pendingBlock)

		case <-h.quitCh:
			return
		}
	}
}

// PendingImpeachBlockBroadcastLoop loops to broadcasts pending impeachment block
func (h *Handler) PendingImpeachBlockBroadcastLoop() {
	for {
		select {
		case impeachBlock := <-h.pendingImpeachBlockCh:

			if h.mode == LBFT2Mode {
				size, r, err := rlp.EncodeToReader(impeachBlock)
				if err != nil {
					log.Warn("failed to encode composed impeach block", "err", err)
					continue
				}
				msg := p2p.Msg{Code: PreprepareImpeachBlockMsg, Size: uint32(size), Payload: r}

				var (
					number = impeachBlock.NumberU64()
					hash   = impeachBlock.Hash()
				)

				if !h.impeachmentRecord.ifImpeached(number, hash) {
					// notify other validators
					go h.BroadcastPreprepareImpeachBlock(impeachBlock)

					// handle the impeach block
					go h.handleLBFT2Msg(msg, nil)

					h.impeachmentRecord.markAsImpeached(number, hash)
				}
			}

		case <-h.quitCh:
			return
		}
	}
}
