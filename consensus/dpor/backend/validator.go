package backend

import (
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/p2p"
)

// handleLbftMsg handles given msg with lbft (lightweighted bft) mode
func (vh *Handler) handleLbftMsg(msg p2p.Msg, p *RemoteValidator) error {

	// TODO: @liuq fix this.
	switch {
	case msg.Code == PrepreparePendingBlockMsg:
		// sign the block and broadcast PrepareSignedHeaderMsg

		block, err := RecoverBlockFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}

		log.Debug("received preprepare block", "number", block.NumberU64(), "hash", block.Hash().Hex())

		localBlock, err := vh.GetPendingBlock(block.NumberU64())
		if localBlock != nil && err == nil && localBlock.Block != nil {
			if localBlock.Status == Inserted {
				// go h.broadcastBlockFn(localBlock.Block, true)
				return nil
			}
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
			switch e := vh.dpor.SignHeader(header, consensus.Preparing); e {
			case nil:

				log.Debug("signed preprepare header, adding to pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

				// add block to pending block cache of blockchain
				if err := vh.AddPendingBlock(block.WithSeal(header)); err != nil {
					return err
				}

				log.Debug("broadcasting signed prepare header to other validators", "number", block.NumberU64(), "hash", block.Hash().Hex())

				// broadcast prepare msg
				go vh.BroadcastPrepareSignedHeader(header)

				return nil

			default:

				if !vh.dpor.HasBlockInChain(block.Hash(), block.NumberU64()) {
					go vh.BroadcastMinedBlock(block)
				}

				log.Warn("err when signing header", "hash", header.Hash, "number", header.Number.Uint64(), "err", err)
				return nil
			}

		default:
			log.Warn("err when validating block", "hash", block.Hash(), "number", block.NumberU64(), "err", err)
			return err
		}

	case msg.Code == PrepareSignedHeaderMsg:
		// add sigs to the header and broadcast, if ready to accept, accept

		header, err := RecoverHeaderFromMsg(msg, p.Peer)
		if err != nil {
			return err
		}
		log.Debug("received signed prepare header", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

		// verify the signed header
		// if correct, insert the block into chain, broadcast it
		switch err := vh.dpor.VerifyHeaderWithState(header, consensus.Committing); err {
		case nil:
			// with enough prepare sigs

			log.Debug("verified signed prepare header", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			block, err := vh.GetPendingBlock(header.Number.Uint64())
			if block == nil || block.Block == nil {
				// TODO: remove this line
				return nil
			}

			log.Debug("inserting block to block chain", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			blk := block.Block.WithSeal(header)
			err = vh.dpor.InsertChain(blk)
			if err != nil {
				log.Warn("err when inserting header", "hash", block.Hash(), "number", block.NumberU64(), "err", err)
				return err
			}

			log.Debug("broadcasting block to other peers", "number", header.Number.Uint64(), "hash", header.Hash().Hex())
			// broadcast the block
			go vh.dpor.BroadcastBlock(blk, true)
			go vh.dpor.BroadcastBlock(blk, false)

			err = vh.AddPendingBlock(blk)
			if err != nil {
				// TODO: remove this
				return nil
			}

			err = vh.UpdateBlockStatus(block.NumberU64(), Inserted)
			if err != nil {
				log.Warn("err when updating block status", "number", block.NumberU64(), "err", err)
				return nil
			}

		case consensus.ErrNotEnoughSigs:
			// sign the block

			log.Debug("without enough sigs in siged prepare header", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

			switch e := vh.dpor.VerifyHeaderWithState(header, consensus.Committing); e {
			case nil:

				log.Debug("signed prepare header, broadcasting...", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

				go vh.BroadcastPrepareSignedHeader(header)

			default:

				// TODO: remove this
				block, err := vh.GetPendingBlock(header.Number.Uint64())
				if block != nil && block.Block != nil && vh.dpor.HasBlockInChain(header.Hash(), header.Number.Uint64()) {
					vh.BroadcastMinedBlock(block.Block)
					return nil
				}

				log.Warn("err when signing header", "hash", header.Hash(), "number", header.Number.Uint64(), "err", err)
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

func (vh *Handler) handlePbftMsg(msg p2p.Msg, p *RemoteValidator) error {
	switch vh.dpor.Status().State {
	case consensus.Prepreparing:
		// if leader, send mined block with preprepare msg, enter preprepared
		// if not leader, wait for a new preprepare block, verify basic field, enter preprepared
		// if timer expired, send new empty block, enter preprepared

		vh.handlePreprepareMsg(msg, p)

	case consensus.Preparing:

		// broadcast prepare msg

		// wait for enough(>2f+1, >2/3) prepare msg, if true, enter prepared
		vh.handlePrepareMsg(msg, p)

	case consensus.Committing:

		// broadcast commit msg

		// wait for enough commit msg, if true, enter committed
		vh.handleCommitMsg(msg, p)

	case consensus.Validating:
		// insert block to chain, if succeed, enter finalcommitted

	case consensus.Inserting:
		// broadcast block to normal peers, once finished, enter newround

	default:
		return consensus.ErrUnknownPbftState
	}

	return nil
}

// handlePreprepareMsg handles received preprepare msg
func (vh *Handler) handlePreprepareMsg(msg p2p.Msg, p *RemoteValidator) error {
	switch {
	case msg.Code == PrepreparePendingBlockMsg:

		block, err := RecoverBlockFromMsg(msg, p.Peer)
		if err != nil {
			// TODO: fix this
			return err
		}

		// Verify the block
		// if correct, sign it and broadcast as Prepare msg
		header := block.RefHeader()

		// add block to pending block cache of blockchain
		if err := vh.AddPendingBlock(block); err != nil {
			return err
		}

		// TODO: add empty view change block verification here

		switch err := vh.dpor.ValidateBlock(block); err {
		// basic fields are correct
		case nil:

			// sign the block
			switch e := vh.dpor.SignHeader(header, consensus.Preparing); e {
			case nil:

				// broadcast prepare msg
				go vh.BroadcastPrepareSignedHeader(header)

				// update dpor status
				vh.dpor.StatusUpdate()

				// now preparing

			default:
				return e
			}

		default:
			return err
		}

	case msg.Code == PrepareSignedHeaderMsg:

	default:
		log.Warn("receievd unwelcome msg in state Preprepare", "msg code", msg.Code)
	}
	return nil
}

func (vh *Handler) handlePrepareMsg(msg p2p.Msg, p *RemoteValidator) error {
	switch {
	case msg.Code == PrepareSignedHeaderMsg:

		// retrieve the header
		var header *types.Header
		if err := msg.Decode(&header); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		// verify the signed header
		// if correct, rebroadcast it as Commit msg
		switch err := vh.dpor.VerifyHeaderWithState(header, consensus.Committing); err {

		// with enough prepare sigs
		case nil:
			// sign the block
			switch e := vh.dpor.SignHeader(header, consensus.Committing); e {
			case nil:

				// broadcast prepare msg
				go vh.BroadcastCommitSignedHeader(header)

				vh.dpor.StatusUpdate()
				// now prepared

			default:
				return e
			}

		default:
		}

	default:
		log.Warn("receievd unwelcome msg in state Prepare", "msg code", msg.Code)
	}
	return nil
}

func (vh *Handler) handleCommitMsg(msg p2p.Msg, p *RemoteValidator) error {
	switch {
	case msg.Code == CommitSignedHeaderMsg:

		// Verify the signed header
		// if correct, add the block to chain

		// retrieve the header
		var header *types.Header
		if err := msg.Decode(&header); err != nil {
			return errResp(ErrDecode, "msg %v: %v", msg, err)
		}

		switch err := vh.dpor.VerifyHeaderWithState(header, consensus.Validating); err {

		// with enough commit sigs
		case nil:

			// update dpor state and pbftstatus
			vh.dpor.StatusUpdate()
			// now committed

			if block, err := vh.GetPendingBlock(header.Number.Uint64()); block != nil && err == nil {

				blk := block.WithSeal(header)

				// insert into chain
				if err := vh.dpor.InsertChain(blk); err != nil {
					return err
				}

				// update dpor state and pbftstatus
				vh.dpor.StatusUpdate()
				// now final-committed

				// broadcast the block
				go vh.dpor.BroadcastBlock(blk, true)
				go vh.dpor.BroadcastBlock(blk, false)

				// update dpor state and pbftstatus
				vh.dpor.StatusUpdate()
				// now new-round

			}

		default:
		}

	default:
		log.Warn("receievd unwelcome msg in state Prepare", "msg code", msg.Code)
	}

	return nil
}

// ReadyToImpeach returns if its time to impeach leader
func (vh *Handler) ReadyToImpeach() bool {
	snap := vh.snap
	head := vh.dpor.Status()

	if head.Head.Number.Uint64() <= snap.Head.Number.Uint64() {
		return true
	}

	vh.snap = head
	return false
}
