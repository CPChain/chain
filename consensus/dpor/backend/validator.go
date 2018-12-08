package backend

import (
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/p2p"
)

// handlePbftMsg handles given msg with pbft mode
func (vh *Handler) handlePbftMsg(msg p2p.Msg, p *RemoteValidator) error {

	input, inputType, msgCode := interface{}(nil), NoType, NoMsgCode

	switch msg.Code {
	case PreprepareBlockMsg:
		block, err := RecoverBlockFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		input, inputType, msgCode = block, BlockType, PreprepareMsgCode

		log.Debug("received preprepare block msg", "number", block.NumberU64())

	case PrepareHeaderMsg:
		header, err := RecoverHeaderFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		input, inputType, msgCode = header, HeaderType, PrepareMsgCode

		log.Debug("received prepare header msg", "number", header.Number.Uint64())

	case CommitHeaderMsg:
		header, err := RecoverHeaderFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		input, inputType, msgCode = header, HeaderType, CommitMsgCode

		log.Debug("received commit header msg", "number", header.Number.Uint64())

	// case PreprepareImpeachBlockMsg:
	// 	block, err := RecoverBlockFromMsg(msg, p.Peer)
	// 	if err != nil {
	// 		return err
	// 	}

	// 	err = vh.knownBlocks.AddBlock(block)
	// 	if err != nil {
	// 		return err
	// 	}

	// 	input, inputType, msgCode = block, blockType, impeachPreprepareMsgCode

	// 	log.Debug("received preprepare impeach block msg", "number", block.NumberU64())

	case PrepareImpeachHeaderMsg:
		header, err := RecoverHeaderFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		input, inputType, msgCode = header, HeaderType, ImpeachPrepareMsgCode

		log.Debug("received prepare impeach header msg", "number", header.Number.Uint64())

	case CommitImpeachHeaderMsg:
		header, err := RecoverHeaderFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		input, inputType, msgCode = header, HeaderType, ImpeachCommitMsgCode

		log.Debug("received commit impeach header msg", "number", header.Number.Uint64())

	default:
		return nil
	}

	output, act, dtype, msgCode, err := vh.fsm.Fsm(input, inputType, msgCode)

	// fsm results
	_, _, _, _, _ = output, act, dtype, msgCode, err

	switch act {
	case BroadcastMsgAction:
		switch dtype {
		case HeaderType:
			header := output.(*types.Header)

			switch msgCode {
			case PrepareMsgCode:
				go vh.BroadcastPrepareHeader(header)

				log.Debug("broadcasted prepare header", "number", header.Number.Uint64())

			case CommitMsgCode:
				go vh.BroadcastCommitHeader(header)

				log.Debug("broadcasted commit header", "number", header.Number.Uint64())

			case ImpeachPrepareMsgCode:
				go vh.BroadcastPrepareImpeachHeader(header)

				log.Debug("broadcasted prepare impeach header", "number", header.Number.Uint64())

			case ImpeachCommitMsgCode:
				go vh.BroadcastCommitImpeachHeader(header)

				log.Debug("broadcasted commit impeach header", "number", header.Number.Uint64())

			default:
				log.Warn("unknown msg code when broadcasting header", "msg code", msgCode)
			}

		case BlockType:
			block := output.(*types.Block)

			switch msgCode {
			case ValidateMsgCode:
				go vh.dpor.BroadcastBlock(block, true)

				log.Debug("broadcasted validate block", "number", block.NumberU64())

			default:
				log.Warn("unknown msg code when broadcasting block", "msg code", msgCode)
			}

		case ImpeachBlockType:
			block := output.(*types.Block)

			switch msgCode {
			case ImpeachValidateMsgCode:
				go vh.dpor.BroadcastBlock(block, true)

				log.Debug("broadcasted validate impeach block", "number", block.NumberU64())

			default:
				log.Warn("unknown msg code when broadcasting block", "msg code", msgCode)
			}

		case NoType:

		default:
			log.Warn("unknown data code when broadcasting block", "data type", dtype)
		}

	case InsertBlockAction:
		switch dtype {
		case BlockType:
			block := output.(*types.Block)
			err := vh.dpor.InsertChain(block)
			if err != nil {
				return err
			}

			log.Debug("inserted block", "number", block.NumberU64())

		case ImpeachBlockType:
			block := output.(*types.Block)
			err := vh.dpor.InsertChain(block)
			if err != nil {
				return err
			}

			log.Debug("inserted impeach block", "number", block.NumberU64())

		default:
			log.Warn("unknown data type when inserting block", "data type", dtype)
		}

	case BroadcastAndInsertBlockAction:
		switch dtype {
		case BlockType:
			block := output.(*types.Block)
			err := vh.dpor.InsertChain(block)
			if err != nil {
				return err
			}
			go vh.dpor.BroadcastBlock(block, true)

			log.Debug("inserted and broadcasted validate block", "number", block.NumberU64())

		case ImpeachBlockType:
			block := output.(*types.Block)
			err := vh.dpor.InsertChain(block)
			if err != nil {
				return err
			}
			go vh.dpor.BroadcastBlock(block, true)

			log.Debug("inserted and broadcasted validate impeach block", "number", block.NumberU64())

		default:
			log.Warn("unknown data type when inserting and broadcasting block", "data type", dtype)
		}

	case NoAction:

	default:
		log.Warn("unknown action type", "action type", act)
	}

	return nil
}

// handleLbftMsg handles given msg with lbft (lightweighted bft) mode
func (vh *Handler) handleLbftMsg(msg p2p.Msg, p *RemoteValidator) error {

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

	if current == nil {
		return false
	}

	if snap != nil {
		if current.Head.Number.Uint64() <= snap.Head.Number.Uint64() {
			return true
		}
	}

	vh.snap = current
	return false
}
