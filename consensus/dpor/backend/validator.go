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

	return nil
}

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
			switch e := vh.dpor.SignHeader(header, consensus.Preparing); e {
			case nil:

				log.Debug("signed preprepare header, adding to pending blocks", "number", block.NumberU64(), "hash", block.Hash().Hex())

				// add block to pending block cache of blockchain
				if err := vh.knownBlocks.AddBlock(block.WithSeal(header)); err != nil {
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

				log.Warn("err when signing header", "hash", header.Hash().Hex(), "number", header.Number.Uint64(), "err", e)
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

			switch e := vh.dpor.SignHeader(header, consensus.Committing); e {
			case nil:

				log.Debug("signed prepare header, broadcasting...", "number", header.Number.Uint64(), "hash", header.Hash().Hex())

				go vh.BroadcastPrepareSignedHeader(header)

			default:

				// TODO: remove this
				block, err := vh.knownBlocks.GetBlock(header.Number.Uint64())
				if block != nil && !vh.dpor.HasBlockInChain(header.Hash(), header.Number.Uint64()) {
					vh.BroadcastMinedBlock(block)
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
