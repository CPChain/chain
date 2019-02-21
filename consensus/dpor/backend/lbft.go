package backend

import (
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"github.com/ethereum/go-ethereum/p2p"
)

// LBFT is the 1.0 version for lbft protocol within validator committee
type LBFT struct {
	handler *Handler
}

// NewLBFT creates an LBFT instance
func NewLBFT(handler *Handler) *LBFT {
	return &LBFT{
		handler: handler,
	}
}

// Handle handles a msg from remote peer(proposer or validator)
func (l *LBFT) Handle(msg p2p.Msg, p *RemoteSigner) error {
	vh := l.handler
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

		// reBoradcast the block
		go vh.reBroadcast(NewBOHFromBlock(block), PreprepareMsgCode, msg)

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
			switch e := vh.dpor.SignHeader(header, consensus.Commit); e {
			case nil:
				// succeed to sign

				log.Debug("signed preprepare block, broadcasting", "number", number, "hash", hash.Hex())

				// broadcast commit msg
				go vh.BroadcastCommitHeader(header)
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
			go vh.BroadcastPreprepareBlock(block)
			return nil

		case consensus.ErrUnknownAncestor:
			// if the block is a unknown ancestor block,
			// wait for its ancestors
			go vh.BroadcastPreprepareBlock(block)
			return nil

		default:
			log.Warn("err when validating block", "hash", block.Hash(), "number", block.NumberU64(), "err", err)
			return err
		}

	case msg.Code == CommitHeaderMsg:

		// recover header from the msg
		header, err := RecoverHeaderFromMsg(msg, p)
		if err != nil {
			return err
		}

		var (
			number = header.Number.Uint64()
			hash   = header.Hash()
		)

		log.Debug("received signed commit header", "number", number, "hash", hash.Hex(), "signatures", header.Dpor.SigsFormatText())

		if vh.dpor.HasBlockInChain(hash, number) {
			return nil
		}

		// reBoradcast the header
		go vh.reBroadcast(NewBOHFromHeader(header), CommitMsgCode, msg)

		// verify the prepare header
		// if correct, insert the block into chain, then broadcast it
		switch err := vh.dpor.VerifyHeaderWithState(header, consensus.Commit); err {

		case nil:
			// there are with enough commit signatures in the header

			log.Debug("verified signed commit header", "number", number, "hash", hash.Hex())

			// if the block body of the header is not found and it's not in local chain
			// broadcast the header again
			block, err := vh.knownBlocks.GetBlock(BlockIdentifier{number: number, hash: hash})
			if block == nil {
				go vh.BroadcastCommitHeader(header)
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
					vh.handleLBFTMsg(msg, p)
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

			log.Debug("without enough signatures in signed commit header", "number", number, "hash", hash.Hex())

			// sign the header
			switch e := vh.dpor.SignHeader(header, consensus.Commit); e {
			case nil:
				// signed the header, everything is ok!

				log.Debug("signed commit header, broadcasting...", "number", number, "hash", hash.Hex())
				go vh.BroadcastCommitHeader(header)

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
