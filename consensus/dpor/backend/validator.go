package backend

import (
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/rlp"
)

// handlePbftMsg handles given msg with pbft mode
func (vh *Handler) handlePbftMsg(msg p2p.Msg, p *RemoteSigner) error {

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
func (vh *Handler) handleLbftMsg(msg p2p.Msg, p *RemoteSigner) error {

	switch {
	case msg.Code == PreprepareBlockMsg:

		// recover the block from msg
		block, err := RecoverBlockFromMsg(msg, p)
		if err != nil {
			return err
		}

		var (
			number = block.NumberU64()
			hash   = block.Hash()
			header = block.Header()
		)

		log.Debug("received preprepare block", "number", number, "hash", hash.Hex())

		// if the block is already in local chain, return nil
		if vh.dpor.HasBlockInChain(hash, number) {
			return nil
		}

		log.Debug("adding to pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

		// add block to pending block cache
		if err := vh.knownBlocks.AddBlock(block); err != nil {
			return err
		}

		// Verify the block
		// if correct, sign it and broadcast as Prepare msg
		switch err := vh.dpor.ValidateBlock(block, false, false); err {
		case nil:
			// basic fields are correct

			log.Debug("validated preprepare block", "number", number, "hash", hash.Hex())

			// sign the block
			switch e := vh.dpor.SignHeader(header, consensus.Preprepared); e {
			case nil:
				// succeed to sign

				log.Debug("signed preprepare block, broadcasting", "number", number, "hash", hash.Hex())

				// broadcast prepare msg
				go vh.BroadcastPrepareHeader(header)
				return nil

			default:
				// if the block is not in the chain, and fail to sign the block,
				// just broadcast the original block to other validators
				if !vh.dpor.HasBlockInChain(hash, number) {
					go vh.BroadcastPreprepareBlock(block)
				}

				log.Warn("err when signing header", "number", number, "hash", hash.Hex(), "err", e)
				return nil
			}

		case consensus.ErrFutureBlock:
			// if the block is a future block,
			// wait for its time
			_ = vh.knownBlocks.AddFutureBlock(block)
			go vh.BroadcastPreprepareBlock(block)
			return nil

		case consensus.ErrUnknownAncestor:
			// if the block is a unknown ancestor block,
			// wait for its ancestors
			_ = vh.knownBlocks.AddUnknownAncestor(block)
			go vh.BroadcastPreprepareBlock(block)
			return nil

		default:
			log.Warn("err when validating block", "hash", block.Hash(), "number", block.NumberU64(), "err", err)
			return err
		}

	case msg.Code == PrepareHeaderMsg:

		// recover header from the msg
		header, err := RecoverHeaderFromMsg(msg, p)
		if err != nil {
			return err
		}

		var (
			number = header.Number.Uint64()
			hash   = header.Hash()
		)

		log.Debug("received signed prepare header", "number", number, "hash", hash.Hex(), "signatures", header.Dpor.SigsFormatText())

		// verify the prepare header
		// if correct, insert the block into chain, then broadcast it
		switch err := vh.dpor.VerifyHeaderWithState(header, consensus.Prepared); err {

		case nil:
			// there are with enough prepare signatures in the header

			log.Debug("verified signed prepare header", "number", number, "hash", hash.Hex())

			// if the block body of the header is not found and it's not in local chain
			// broadcast the header again
			block, err := vh.knownBlocks.GetBlock(header.Number.Uint64())
			if block == nil {
				if !vh.dpor.HasBlockInChain(header.Hash(), header.Number.Uint64()) {
					go vh.BroadcastPrepareHeader(header)
				}
				return nil
			}

			log.Debug("inserting block to block chain", "number", number, "hash", hash.Hex())

			// insert the block with signed and sealed header into local chain
			blk := block.WithSeal(header)
			err = vh.dpor.InsertChain(blk)
			if err != nil {
				log.Warn("err when inserting header", "number", number, "hash", hash.Hex(), "err", err)
				return err
			}

			// broadcast the block
			log.Debug("broadcasting block to other peers", "number", number, "hash", hash.Hex())
			go vh.dpor.BroadcastBlock(blk, true)  // broadcast the block to some random peers (root of peer set size)
			go vh.dpor.BroadcastBlock(blk, false) // broadcast the block header to other peers

			// update known blocks cache
			err = vh.knownBlocks.AddBlock(blk)
			if err != nil {
				return nil
			}

		case consensus.ErrFutureBlock:
			// it is a future header, wait for its time to verify it again

			delay := time.Duration((header.Time.Int64() - (time.Now().UnixNano() * int64(time.Nanosecond) / int64(time.Millisecond))) * int64(time.Millisecond) / int64(time.Nanosecond))

			log.Debug("received future block header", "number", number, "hash", hash.Hex())
			log.Debug("delay of future block header", "delay", delay)

			// if delay is less than 10 seconds, wait for it
			if delay <= 1e10 {
				go func() {
					<-time.After(delay)
					vh.handleLbftMsg(msg, p)
				}()
			}

			// if delay is large than 10 seconds, return nothing
			return nil

		case consensus.ErrUnknownAncestor:
			// TODO: sync with msg sender
			log.Warn("unhandled unknown ancestor err", "number", number, "hash", hash.Hex(), "err", err)

		case consensus.ErrNotEnoughSigs:
			// it is a normal header without enough signatures on it,
			// sign it, broadcast it

			log.Debug("without enough signatures in signed prepare header", "number", number, "hash", hash.Hex())

			// sign the header
			switch e := vh.dpor.SignHeader(header, consensus.Prepared); e {
			case nil:
				// signed the header, everything is ok!

				log.Debug("signed prepare header, broadcasting...", "number", number, "hash", hash.Hex())
				go vh.BroadcastPrepareHeader(header)

				// switch err := vh.dpor.VerifyHeaderWithState(header, consensus.Prepared); err {
				// case nil:

				// 	// if the block body of the header is not found and it's not in local chain
				// 	// broadcast the header again
				// 	block, err := vh.knownBlocks.GetBlock(header.Number.Uint64())
				// 	if block == nil && !vh.dpor.HasBlockInChain(header.Hash(), header.Number.Uint64()) {
				// 		go vh.BroadcastPrepareHeader(header)
				// 		return nil
				// 	}

				// 	log.Debug("inserting block to local chain", "number", number, "hash", hash.Hex())

				// 	// If now there are enough signatures, insert the block of the header into local chain
				// 	blk := block.WithSeal(header)
				// 	err = vh.dpor.InsertChain(blk)
				// 	if err != nil {
				// 		log.Warn("err when inserting header", "number", number, "hash", hash.Hex(), "err", err)
				// 		return err
				// 	}

				// 	// broadcast the block
				// 	log.Debug("broadcasting block to other peers", "number", number, "hash", hash.Hex())
				// 	go vh.dpor.BroadcastBlock(blk, true)  // broadcast the block to some random peers (root of peer set size)
				// 	go vh.dpor.BroadcastBlock(blk, false) // broadcast the block header to other peers

				// 	// update known blocks cache
				// 	err = vh.knownBlocks.AddBlock(blk)
				// 	if err != nil {
				// 		return nil
				// 	}

				// default:
				// 	go vh.BroadcastPrepareHeader(header)
				// }

				return nil

			default:
				// failed to sign the header!

				// log warning!
				log.Warn("err when signing header", "number", number, "hash", hash.Hex(), "err", err)

				return nil
			}

		default:
			log.Warn("err when verifying header", "number", number, "hash", hash.Hex(), "err", err)
			return err
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

func (vh *Handler) procUnhandledBlocks() {
	timer := time.NewTicker(200 * time.Millisecond)
	defer timer.Stop()

	for {
		select {
		case <-timer.C:
			for _, n := range vh.knownBlocks.GetFutureBlockNumbers() {
				// get the block
				blk, _ := vh.knownBlocks.GetFutureBlock(n.(uint64))

				// make a msg
				size, r, err := rlp.EncodeToReader(blk)
				if err != nil {
					continue
				}
				msg := p2p.Msg{Code: PreprepareBlockMsg, Size: uint32(size), Payload: r}

				// handle it as received from remote unknown peer
				err = vh.handleLbftMsg(msg, nil)
				if err == nil {
					vh.knownBlocks.futureBlocks.Remove(n)
				}
			}

			for _, n := range vh.knownBlocks.GetUnknownAncestorBlockNumbers() {
				// get the block
				blk, _ := vh.knownBlocks.GetUnknownAncestor(n.(uint64))

				// make a msg
				size, r, err := rlp.EncodeToReader(blk)
				if err != nil {
					continue
				}
				msg := p2p.Msg{Code: PreprepareBlockMsg, Size: uint32(size), Payload: r}

				// handle it as received from remote unknown peer
				err = vh.handleLbftMsg(msg, nil)
				if err == nil {
					vh.knownBlocks.unknownAncestors.Remove(n)
				}
			}

		case <-vh.quitCh:
			return
		}
	}
}
