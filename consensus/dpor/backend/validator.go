package backend

import (
	"time"

	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/rlp"
)

// handlePbftMsg handles given msg with pbft mode
// func (vh *Handler) handlePbftMsg(msg p2p.Msg, p *RemoteSigner) error {

// 	input, msgCode := (*blockOrHeader)(nil), NoMsgCode

// 	switch msg.Code {
// 	case PreprepareBlockMsg:
// 		block, err := RecoverBlockFromMsg(msg, p.Peer)
// 		if err != nil {
// 			return err
// 		}

// 		input, msgCode = &blockOrHeader{block: block}, PreprepareMsgCode

// 		log.Debug("received preprepare block msg", "number", block.NumberU64())

// 	case PrepareHeaderMsg:
// 		header, err := RecoverHeaderFromMsg(msg, p.Peer)
// 		if err != nil {
// 			return err
// 		}

// 		input, msgCode = &blockOrHeader{header: header}, PrepareMsgCode

// 		log.Debug("received prepare header msg", "number", header.Number.Uint64())

// 	case CommitHeaderMsg:
// 		header, err := RecoverHeaderFromMsg(msg, p.Peer)
// 		if err != nil {
// 			return err
// 		}

// 		input, msgCode = &blockOrHeader{header: header}, CommitMsgCode

// 		log.Debug("received commit header msg", "number", header.Number.Uint64())

// 	case ValidateBlockMsg:
// 		block, err := RecoverBlockFromMsg(msg, p.Peer)
// 		if err != nil {
// 			return err
// 		}

// 		input, msgCode = &blockOrHeader{block: block}, ValidateMsgCode

// 		log.Debug("received validate block msg", "number", block.NumberU64())

// 	case PrepareImpeachHeaderMsg:
// 		header, err := RecoverHeaderFromMsg(msg, p.Peer)
// 		if err != nil {
// 			return err
// 		}

// 		input, msgCode = &blockOrHeader{header: header}, ImpeachPrepareMsgCode

// 		log.Debug("received prepare impeach header msg", "number", header.Number.Uint64())

// 	case CommitImpeachHeaderMsg:
// 		header, err := RecoverHeaderFromMsg(msg, p.Peer)
// 		if err != nil {
// 			return err
// 		}

// 		input, msgCode = &blockOrHeader{header: header}, ImpeachCommitMsgCode

// 		log.Debug("received commit impeach header msg", "number", header.Number.Uint64())

// 	case ValidateImpeachBlockMsg:
// 		block, err := RecoverBlockFromMsg(msg, p.Peer)
// 		if err != nil {
// 			return err
// 		}

// 		input, msgCode = &blockOrHeader{block: block}, ImpeachValidateMsgCode

// 		log.Debug("received impeach validate block msg", "number", block.NumberU64())

// 	default:
// 		return nil
// 	}

// 	output, act, msgCode, err := vh.fsm.FSM(input, msgCode)

// 	// fsm results
// 	_, _, _, _ = output, act, msgCode, err

// 	log.Debug("fsm result", "act", act, "data type", "msg code", msgCode, "err", err)

// 	switch act {
// 	case BroadcastMsgAction:
// 		if output.isHeader() {
// 			header := output.header

// 			switch msgCode {
// 			case PrepareMsgCode:
// 				go vh.BroadcastPrepareHeader(header)

// 				log.Debug("broadcast prepare header", "number", header.Number.Uint64())

// 			case CommitMsgCode:
// 				go vh.BroadcastCommitHeader(header)

// 				log.Debug("broadcast commit header", "number", header.Number.Uint64())

// 			case ImpeachPrepareMsgCode:
// 				go vh.BroadcastPrepareImpeachHeader(header)

// 				log.Debug("broadcast prepare impeach header", "number", header.Number.Uint64())

// 			case ImpeachCommitMsgCode:
// 				go vh.BroadcastCommitImpeachHeader(header)

// 				log.Debug("broadcast commit impeach header", "number", header.Number.Uint64())

// 			default:
// 				log.Warn("unknown msg code when broadcasting header", "msg code", msgCode)
// 			}

// 		} else if output.isBlock() {

// 			block := output.block

// 			switch msgCode {
// 			case ValidateMsgCode:
// 				go vh.BroadcastValidateBlock(block)

// 				log.Debug("broadcast validate block", "number", block.NumberU64())

// 			case ImpeachValidateMsgCode:
// 				go vh.BroadcastValidateImpeachBlock(block)

// 				log.Debug("broadcast validate impeach block", "number", block.NumberU64())

// 			default:
// 				log.Warn("unknown msg code when broadcasting block", "msg code", msgCode)
// 			}

// 		} else {

// 			log.Warn("unknown data code when broadcasting block", "data type", output)
// 		}

// 	case InsertBlockAction:
// 		if output.isBlock() {
// 			block := output.block

// 			err := vh.dpor.InsertChain(block)
// 			if err != nil {
// 				return err
// 			}

// 			log.Debug("inserted block", "number", block.NumberU64())

// 		} else {

// 			log.Warn("unknown data type when inserting block", "output", output)
// 		}

// 	case BroadcastAndInsertBlockAction:
// 		if output.isBlock() {

// 			block := output.block
// 			err := vh.dpor.InsertChain(block)
// 			if err != nil {
// 				return err
// 			}

// 			switch msgCode {
// 			case ValidateMsgCode:
// 				go vh.BroadcastValidateBlock(block)

// 				log.Debug("broadcast validate block", "number", block.NumberU64())

// 			case ImpeachValidateMsgCode:
// 				go vh.BroadcastValidateImpeachBlock(block)

// 				log.Debug("broadcast validate impeach block", "number", block.NumberU64())

// 			default:
// 				log.Warn("unknown msg code when broadcasting block", "msg code", msgCode)
// 			}
// 			go vh.dpor.BroadcastBlock(block, true)

// 			log.Debug("inserted and broadcast validate block", "number", block.NumberU64())

// 		} else {

// 			log.Warn("unknown data type when inserting and broadcasting block", "output", output)
// 		}

// 	// case BroadcastMultipleMsgAction:
// 	// 	switch dtype {
// 	// 	case HeaderType:
// 	// 		log.Debug("type of output", "type", reflect.TypeOf(output))
// 	// 		headers := output
// 	// 		if len(headers) != 2 {
// 	// 			log.Error("wrong size of BroadcastMultipleMsgAction", "len", len(headers))
// 	// 		}
// 	// 		prepareHeader, commitHeader := headers[0].(*types.Header), headers[1].(*types.Header)

// 	// 		go vh.BroadcastPrepareHeader(prepareHeader)
// 	// 		go vh.BroadcastCommitHeader(commitHeader)

// 	// 		log.Debug("broadcasted prepare msg with BroadcastMultipleMsgAction", "number", prepareHeader.Number.Uint64())
// 	// 		log.Debug("broadcasted commit msg with BroadcastMultipleMsgAction", "number", commitHeader.Number.Uint64())

// 	// 	default:
// 	// 		log.Warn("unknown data type when broadcast multiple msg", "data type", dtype)
// 	// 	}

// 	case NoAction:
// 		log.Warn("no action returned")

// 	default:
// 		log.Warn("unknown action type", "action type", act)
// 	}

// 	return nil
// }

// handleLBFTMsg handles given msg with lbft (lightweighted bft) mode
func (vh *Handler) handleLBFTMsg(msg p2p.Msg, p *RemoteSigner) error {
	if vh.lbft == nil {
		vh.lbft = NewLBFT(vh)
	}

	return vh.lbft.Handle(msg, p)
}

func (vh *Handler) handleLBFT2Msg(msg p2p.Msg, p *RemoteSigner) error {
	switch msg.Code {
	case PreprepareBlockMsg:
		// recover the block from msg
		block, err := RecoverBlockFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input := &blockOrHeader{
			block: block,
		}
		msgCode := PreprepareMsgCode

		// call fsm
		output, action, msgCode, err := vh.fsm.FSM(input, msgCode)
		if err != nil {
			return err
		}

		// if there is a output, the action is broadcast, msg code is prepare msg, and err is nil,
		// broadcast the header with prepare header msg
		if output != nil && action == BroadcastMsgAction && msgCode == PrepareMsgCode && err == nil {
			go vh.BroadcastPrepareHeader(output[0].header)
		}
		return nil

	case PrepareHeaderMsg:
		// recover the header from msg
		header, err := RecoverHeaderFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input := &blockOrHeader{
			header: header,
		}
		msgCode := PrepareMsgCode

		// call fsm
		output, action, msgCode, err := vh.fsm.FSM(input, msgCode)
		if err != nil {
			return err
		}

		// if the action is broadcast and output is not nil
		if output != nil && action == BroadcastMsgAction && err == nil {
			switch msgCode {
			// broadcast prepare msg
			case PrepareMsgCode:
				go vh.BroadcastPrepareHeader(output[0].header)

			// broadcast commit msg
			case CommitMsgCode:
				go vh.BroadcastCommitHeader(output[0].header)

			case PrepareAndCommitMsgCode:
				go vh.BroadcastPrepareHeader(output[0].header)
				go vh.BroadcastCommitHeader(output[1].header)

			default:
			}
		}
		return nil

	case CommitHeaderMsg:
		// recover the header from msg
		header, err := RecoverHeaderFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input := &blockOrHeader{
			header: header,
		}
		msgCode := CommitMsgCode

		// call fsm
		output, action, msgCode, err := vh.fsm.FSM(input, msgCode)
		if err != nil {
			return err
		}

		// if the action is broadcast and output is not nil
		if output != nil && action == BroadcastMsgAction && err == nil {
			switch msgCode {
			// broadcast commit msg
			case CommitMsgCode:
				go vh.BroadcastCommitHeader(output[0].header)

			// broadcast validate msg
			case ValidateMsgCode:
				go vh.BroadcastValidateBlock(output[0].block)

			default:
			}
		}
		return nil

	case ValidateBlockMsg:
		// recover the block from msg
		block, err := RecoverBlockFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input := &blockOrHeader{
			block: block,
		}
		msgCode := ValidateMsgCode

		// do nothing with the result
		_, _, _, err = vh.fsm.FSM(input, msgCode)
		if err != nil {
			return err
		}
		return nil

	case PreprepareImpeachBlockMsg:
		// recover the block from msg
		block, err := RecoverBlockFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input := &blockOrHeader{
			block: block,
		}
		msgCode := ImpeachPreprepareMsgCode

		// call fsm
		output, action, msgCode, err := vh.fsm.FSM(input, msgCode)
		if err != nil {
			return err
		}

		// if there is a output, the action is broadcast, msg code is prepare msg, and err is nil,
		// broadcast the header with prepare header msg
		if output != nil && action == BroadcastMsgAction && msgCode == ImpeachPrepareMsgCode && err == nil {
			go vh.BroadcastPrepareImpeachHeader(output[0].header)
		}
		return nil

	case PrepareImpeachHeaderMsg:
		// recover the header from msg
		header, err := RecoverHeaderFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input := &blockOrHeader{
			header: header,
		}
		msgCode := ImpeachPrepareMsgCode

		// call fsm
		output, action, msgCode, err := vh.fsm.FSM(input, msgCode)
		if err != nil {
			return err
		}

		// if the action is broadcast and output is not nil
		if output != nil && action == BroadcastMsgAction && err == nil {
			switch msgCode {
			// broadcast prepare msg
			case ImpeachPrepareMsgCode:
				go vh.BroadcastPrepareImpeachHeader(output[0].header)

			// broadcast commit msg
			case ImpeachCommitMsgCode:
				go vh.BroadcastCommitImpeachHeader(output[0].header)

			case ImpeachPrepareAndCommitMsgCode:
				go vh.BroadcastPrepareImpeachHeader(output[0].header)
				go vh.BroadcastCommitImpeachHeader(output[1].header)

			default:
			}
		}
		return nil

	case CommitImpeachHeaderMsg:
		// recover the header from msg
		header, err := RecoverHeaderFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input := &blockOrHeader{
			header: header,
		}
		msgCode := ImpeachCommitMsgCode

		// call fsm
		output, action, msgCode, err := vh.fsm.FSM(input, msgCode)
		if err != nil {
			return err
		}

		// if the action is broadcast and output is not nil
		if output != nil && action == BroadcastMsgAction && err == nil {
			switch msgCode {
			// broadcast commit msg
			case ImpeachCommitMsgCode:
				go vh.BroadcastCommitImpeachHeader(output[0].header)

			// broadcast validate msg
			case ValidateImpeachBlockMsg:
				go vh.BroadcastValidateImpeachBlock(output[0].block)
			default:
			}
		}
		return nil

	case ValidateImpeachBlockMsg:
		// recover the block from msg
		block, err := RecoverBlockFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input := &blockOrHeader{
			block: block,
		}
		msgCode := ImpeachValidateMsgCode

		// do nothing with the result
		_, _, _, err = vh.fsm.FSM(input, msgCode)
		if err != nil {
			return err
		}
		return nil

	default:

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
			for _, bi := range vh.knownBlocks.GetFutureBlockIdentifiers() {
				// get the block
				blk, _ := vh.knownBlocks.GetFutureBlock(bi.(blockIdentifier))

				// make a msg
				size, r, err := rlp.EncodeToReader(blk)
				if err != nil {
					continue
				}
				msg := p2p.Msg{Code: PreprepareBlockMsg, Size: uint32(size), Payload: r}

				// handle it as received from remote unknown peer
				err = vh.handleLBFTMsg(msg, nil)
				vh.knownBlocks.futureBlocks.Remove(bi.(blockIdentifier))
			}

			for _, bi := range vh.knownBlocks.GetUnknownAncestorBlockIdentifiers() {
				// get the block
				blk, _ := vh.knownBlocks.GetUnknownAncestor(bi.(blockIdentifier))

				// make a msg
				size, r, err := rlp.EncodeToReader(blk)
				if err != nil {
					continue
				}
				msg := p2p.Msg{Code: PreprepareBlockMsg, Size: uint32(size), Payload: r}

				// handle it as received from remote unknown peer
				err = vh.handleLBFTMsg(msg, nil)
				vh.knownBlocks.unknownAncestors.Remove(bi.(blockIdentifier))
			}

		case <-vh.quitCh:
			return
		}
	}
}

// ReceiveImpeachPendingBlock receives a block to add to pending block channel
func (vh *Handler) ReceiveImpeachPendingBlock(block *types.Block) error {
	select {
	case vh.pendingImpeachBlockCh <- block:
		err := vh.knownBlocks.AddBlock(block)
		if err != nil {
			return err
		}

		return nil
	}
}
