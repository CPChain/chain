package backend

import (
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/p2p"
)

// dialLoop loops to dial remote proposer if local peer is a validator
func (vh *Handler) dialLoop() {

	futureTimer := time.NewTicker(1 * time.Second)
	defer futureTimer.Stop()

	var block *types.Block

	for {
		select {
		case <-futureTimer.C:
			blk := vh.dpor.GetCurrentBlock()
			if block != nil {
				if blk.Number().Cmp(block.Number()) > 0 {
					// if there is an updated block, try to dial future proposers
					number := blk.NumberU64()
					term := vh.dpor.FutureTermOf(number)

					proposers, err := vh.dpor.ProposersOfTerm(term)
					if err != nil {
						log.Warn("err when call proposers of term", "err", err)
					}

					err = vh.dialer.UpdateRemoteProposers(term, proposers)
					if err != nil {
						log.Warn("err when update remote proposers", "err", err)
					}

					go vh.dialer.DialAllRemoteProposers(term)
				}
			}
			block = blk

		case <-vh.quitSync:
			return
		}
	}
}

// handlePbftMsg handles given msg with pbft mode
func (vh *Handler) handlePbftMsg(msg p2p.Msg, p *RemoteValidator) error {

	input, inputType, msgCode := interface{}(nil), noType, noMsgCode

	switch msg.Code {
	case PreprepareBlockMsg:
		block, err := RecoverBlockFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		input, inputType, msgCode = block, blockType, preprepareMsgCode

	case PrepareHeaderMsg:
		header, err := RecoverHeaderFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		input, inputType, msgCode = header, headerType, prepareMsgCode

	case CommitHeaderMsg:
		header, err := RecoverHeaderFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		input, inputType, msgCode = header, headerType, commitMsgCode

	case PreprepareImpeachBlockMsg:
		block, err := RecoverBlockFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		input, inputType, msgCode = block, blockType, impeachPreprepareMsgCode

	case PrepareImpeachHeaderMsg:
		header, err := RecoverHeaderFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		input, inputType, msgCode = header, headerType, impeachPrepareMsgCode

	case CommitImpeachHeaderMsg:
		header, err := RecoverHeaderFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		input, inputType, msgCode = header, headerType, impeachCommitMsgCode

	default:
		return nil
	}

	output, act, dtype, msgCode, err := vh.fsm.Fsm(input, inputType, msgCode)

	// fsm results
	_, _, _, _, _ = output, act, dtype, msgCode, err

	switch act {
	case broadcastMsgAction:
		switch dtype {
		case headerType:
			header := output.(*types.Header)

			switch msgCode {
			case prepareMsgCode:
				vh.BroadcastPrepareHeader(header)

			case commitMsgCode:
				vh.BroadcastCommitHeader(header)

			case impeachPrepareMsgCode:
				vh.BroadcastPrepareImpeachHeader(header)

			case impeachCommitMsgCode:
				vh.BroadcastCommitImpeachHeader(header)

			default:
				log.Warn("unknown msg code when broadcasting header", "msg code", msgCode)
			}

		case blockType:
			block := output.(*types.Block)

			switch msgCode {
			case preprepareMsgCode:
				go vh.BroadcastPreprepareBlock(block)

			default:
				log.Warn("unknown msg code when broadcasting block", "msg code", msgCode)
			}

		case impeachBlockType:
			block := output.(*types.Block)

			switch msgCode {
			case impeachPreprepareMsgCode:
				// TODO: fix this
				go vh.BroadcastPreprepareImpeachBlock(block)

			default:
				log.Warn("unknown msg code when broadcasting block", "msg code", msgCode)
			}

		case noType:

		default:
			log.Warn("unknown data code when broadcasting block", "data type", dtype)
		}

	case insertBlockAction:
		switch dtype {
		case blockType:
			block := input.(*types.Block)
			err := vh.dpor.InsertChain(block)
			if err != nil {
				return err
			}

		case impeachBlockType:
			block := input.(*types.Block)
			err := vh.dpor.InsertChain(block)
			if err != nil {
				return err
			}

		default:
			log.Warn("unknown data type when inserting block", "data type", dtype)
		}

	case broadcastAndInsertBlockAction:
		switch dtype {
		case blockType:
			block := input.(*types.Block)
			err := vh.dpor.InsertChain(block)
			if err != nil {
				return err
			}
			go vh.BroadcastPreprepareBlock(block)

		case impeachBlockType:
			block := input.(*types.Block)
			err := vh.dpor.InsertChain(block)
			if err != nil {
				return err
			}
			// TODO: fix this
			go vh.BroadcastPreprepareImpeachBlock(block)

		default:
			log.Warn("unknown data type when inserting and broadcasting block", "data type", dtype)
		}

	case noAction:

	default:
		log.Warn("unknown action type", "action type", act)
	}

	return nil
}

// handleLbftMsg handles given msg with lbft (lightweighted bft) mode
func (vh *Handler) handleLbftMsg(msg p2p.Msg, p *RemoteValidator) error {

	// TODO: @liuq fix this.
	switch {
	case msg.Code == PreprepareBlockMsg:
		// sign the block and broadcast PrepareSignedHeaderMsg

		block, err := RecoverBlockFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		number := block.NumberU64()
		hash := block.Hash()

		log.Debug("received preprepare block", "number", block.NumberU64(), "hash", block.Hash().Hex())

		if vh.dpor.HasBlockInChain(hash, number) {
			return nil
		}

		// Verify the block
		// if correct, sign it and broadcast as Prepare msg
		// verify header, if basic fields are correct, broadcast prepare msg
		switch err := vh.dpor.ValidateBlock(block); err {
		case nil:
			// basic fields are correct

			log.Debug("validated preprepare block", "number", block.NumberU64(), "hash", block.Hash().Hex())

			// sign the block
			header := block.Header()
			switch e := vh.dpor.SignHeader(header, consensus.Preprepared); e {
			case nil:

				log.Debug("signed preprepare header, adding to pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

				// add block to pending block cache of blockchain
				if err := vh.knownBlocks.AddBlock(block.WithSeal(header)); err != nil {
					return err
				}

				log.Debug("broadcasting signed prepare header to other validators", "number", block.NumberU64(), "hash", block.Hash().Hex())

				// broadcast prepare msg
				go vh.BroadcastPrepareHeader(header)

				return nil

			default:

				if !vh.dpor.HasBlockInChain(block.Hash(), block.NumberU64()) {
					go vh.BroadcastPreprepareBlock(block)
				}

				log.Warn("err when signing header", "hash", header.Hash().Hex(), "number", header.Number.Uint64(), "err", e)
				return nil
			}

		default:
			log.Warn("err when validating block", "hash", block.Hash(), "number", block.NumberU64(), "err", err)
			return err
		}

	case msg.Code == PrepareHeaderMsg:
		// add sigs to the header and broadcast, if ready to accept, accept

		header, err := RecoverHeaderFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}
		log.Debug("received signed prepare header", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

		// verify the signed header
		// if correct, insert the block into chain, broadcast it
		switch err := vh.dpor.VerifyHeaderWithState(header, consensus.Prepared); err {
		case nil:
			// with enough prepare sigs

			log.Debug("verified signed prepare header", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			block, err := vh.knownBlocks.GetBlock(header.Number.Uint64())
			if block == nil {
				// TODO: remove this line
				return nil
			}

			log.Debug("inserting block to block chain", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			blk := block.WithSeal(header)
			err = vh.dpor.InsertChain(blk)
			if err != nil {
				log.Warn("err when inserting header", "hash", block.Hash(), "number", block.NumberU64(), "err", err)
				return err
			}

			log.Debug("broadcasting block to other peers", "number", header.Number.Uint64(), "hash", header.Hash().Hex())
			// broadcast the block
			go vh.dpor.BroadcastBlock(blk, true)
			go vh.dpor.BroadcastBlock(blk, false)

			err = vh.knownBlocks.AddBlock(blk)
			if err != nil {
				// TODO: remove this
				return nil
			}

		case consensus.ErrNotEnoughSigs:
			// sign the block

			log.Debug("without enough sigs in siged prepare header", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			switch e := vh.dpor.SignHeader(header, consensus.Prepared); e {
			case nil:

				log.Debug("signed prepare header, broadcasting...", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

				go vh.BroadcastPrepareHeader(header)

			default:

				// TODO: remove this
				block, err := vh.knownBlocks.GetBlock(header.Number.Uint64())
				if block != nil && !vh.dpor.HasBlockInChain(header.Hash(), header.Number.Uint64()) {
					vh.BroadcastPreprepareBlock(block)
					return nil
				}

				log.Warn("err when signing header", "hash", header.Hash().Hex(), "number", header.Number.Uint64(), "err", err)
				return nil
			}

		default:
			log.Warn("err when verifying header", "hash", header.Hash(), "number", header.Number.Uint64(), "err", err)
		}

	default:
		return consensus.ErrUnknownLbftState
	}
	return nil
}

// ReadyToImpeach returns if its time to impeach leader
func (vh *Handler) ReadyToImpeach() bool {
	snap := vh.snap
	current := vh.dpor.Status()

	if snap == nil || current == nil {
		return false
	}

	if current.Head.Number.Uint64() <= snap.Head.Number.Uint64() {
		return true
	}

	vh.snap = current
	return false
}
