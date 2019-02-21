/*
this is LBFT 2.0
*/

package backend

import (
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
)

// LBFT2 is a state machine used for consensus protocol for validators msg processing
type LBFT2 struct {
	number    uint64
	state     consensus.State
	stateLock sync.RWMutex

	faulty uint64 // faulty is the parameter of 3f+1 nodes in Byzantine
	lock   sync.RWMutex

	dpor       DporService
	blockCache *RecentBlocks // cache of blocks

	prepareSignatures *signaturesForBlockCaches
	commitSignatures  *signaturesForBlockCaches
}

// NewLBFT2 create an LBFT2 instance
func NewLBFT2(faulty uint64, dpor DporService, handleImpeachBlock HandleGeneratedImpeachBlock, db database.Database) *LBFT2 {

	pbft := &LBFT2{
		state:  consensus.Idle,
		faulty: faulty,
		number: dpor.GetCurrentBlock().NumberU64() + 1,
		dpor:   dpor,

		blockCache:        NewRecentBlocks(db),
		prepareSignatures: newSignaturesForBlockCaches(db),
		commitSignatures:  newSignaturesForBlockCaches(db),
	}

	return pbft
}

// Faulty returns the number of faulty nodes
func (p *LBFT2) Faulty() uint64 {
	p.lock.RLock()
	defer p.lock.RUnlock()

	return p.faulty
}

// State returns current state
func (p *LBFT2) State() consensus.State {
	p.stateLock.RLock()
	defer p.stateLock.RUnlock()

	return p.state
}

// SetState sets state of the state machine
func (p *LBFT2) SetState(state consensus.State) {
	p.stateLock.Lock()
	defer p.stateLock.Unlock()

	p.state = state
}

// Number returns current number
func (p *LBFT2) Number() uint64 {
	p.stateLock.RLock()
	defer p.stateLock.RUnlock()

	return p.number
}

// SetNumber sets number of the state machine
func (p *LBFT2) SetNumber(number uint64) {
	p.stateLock.Lock()
	defer p.stateLock.Unlock()

	p.number = number
}

// Status returns current states
func (p *LBFT2) Status() DSMStatus {
	return DSMStatus{
		State:  p.State(),
		Number: p.Number(),
	}
}

// FSM implements ConsensusStateMachine.FSM
func (p *LBFT2) FSM(input *BlockOrHeader, msgCode MsgCode) ([]*BlockOrHeader, Action, MsgCode, error) {
	p.stateLock.Lock()
	defer p.stateLock.Unlock()

	state := p.state
	number := p.number

	log.Debug("current status", "state", state, "number", number, "msg code", msgCode.String(), "input number", input.Number())

	output, action, msgCode, state, err := p.realFSM(input, msgCode, state)
	// output, action, msgCode, state, err := p.fsm(input, msgCode, state)

	if output != nil && err == nil {
		p.state = state
		p.number = output[0].Number()
	}

	log.Debug("result state", "state", state, "number", number, "msg code", msgCode.String(), "action", action)

	if p.number < p.dpor.GetCurrentBlock().NumberU64()+1 {
		p.number = p.dpor.GetCurrentBlock().NumberU64() + 1
		p.state = consensus.Idle
	}

	return output, action, msgCode, err
}

func (p *LBFT2) realFSM(input *BlockOrHeader, msgCode MsgCode, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	var (
		hash   = input.Hash()
		number = input.Number()
	)

	_, _ = hash, number

	// if already in chain, do nothing
	if p.dpor.HasBlockInChain(hash, number) {
		// TODO: add error type
		return nil, NoAction, NoMsgCode, state, nil
	}

	if number < p.number {
		log.Warn("outdated msg", "number", number, "hash", hash.Hex())
		// TODO: add error type
		return nil, NoAction, NoMsgCode, state, nil
	}

	switch state {
	case consensus.Idle:
		return p.IdleHandler(input, msgCode, state)

	case consensus.Prepare:
		return p.PrepareHandler(input, msgCode, state)

	case consensus.Commit:
		return p.CommitHandler(input, msgCode, state)

	case consensus.ImpeachPrepare:
		return p.ImpeachPrepareHandler(input, msgCode, state)

	case consensus.ImpeachCommit:
		return p.ImpeachCommitHandler(input, msgCode, state)

	case consensus.Validate:
		return p.ValidateHandler(input, msgCode, state)

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}

}

// IdleHandler is the handler for Idle state
func (p *LBFT2) IdleHandler(input *BlockOrHeader, msgCode MsgCode, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	switch msgCode {
	case ImpeachPreprepareMsgCode, ImpeachPrepareMsgCode, ImpeachCommitMsgCode, ImpeachValidateMsgCode:

		log.Debug("IdleHandler to call ImpeachHandler")

		return p.ImpeachHandler(input, msgCode, state)

	case PrepareMsgCode, CommitMsgCode, ValidateMsgCode:

		log.Debug("IdleHandler to call PrepareHandler")

		return p.PrepareHandler(input, msgCode, state)

	case PreprepareMsgCode:

		log.Debug("IdleHandler to call handlePreprepareMsg")

		return p.handlePreprepareMsg(input, state, func(block *types.Block) error {
			return p.dpor.ValidateBlock(block, false, true)
		})

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}
}

// PrepareHandler is the handler for Prepare state
func (p *LBFT2) PrepareHandler(input *BlockOrHeader, msgCode MsgCode, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	switch msgCode {
	case ImpeachPreprepareMsgCode, ImpeachPrepareMsgCode, ImpeachCommitMsgCode, ImpeachValidateMsgCode:

		log.Debug("PrepareHandler to call ImpeachHandler")

		return p.ImpeachHandler(input, msgCode, state)

	case CommitMsgCode, ValidateMsgCode:

		log.Debug("PrepareHandler to call CommitHandler")

		return p.CommitHandler(input, msgCode, state)

	case PrepareMsgCode:

		log.Debug("PrepareHandler to call handlePrepareMsg")

		return p.handlePrepareMsg(input, state)

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}
}

// CommitHandler is the handler for Commit state
func (p *LBFT2) CommitHandler(input *BlockOrHeader, msgCode MsgCode, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	switch msgCode {
	case ImpeachPreprepareMsgCode, ImpeachPrepareMsgCode, ImpeachCommitMsgCode, ImpeachValidateMsgCode:

		log.Debug("CommitHandler to call ImpeachHandler")

		return p.ImpeachHandler(input, msgCode, state)

	case ValidateMsgCode:

		log.Debug("CommitHandler to call handleValidateMsg")

		return p.handleValidateMsg(input, state)

	case CommitMsgCode:

		log.Debug("CommitHandler to call handleCommitMsg")

		return p.handleCommitMsg(input, state)

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}
}

// ImpeachHandler is the handler for all impeachment related msg
func (p *LBFT2) ImpeachHandler(input *BlockOrHeader, msgCode MsgCode, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	switch msgCode {
	case ImpeachPrepareMsgCode, ImpeachCommitMsgCode, ImpeachValidateMsgCode:

		log.Debug("ImpeachHandler to call ImpeachPrepareHandler")

		return p.ImpeachPrepareHandler(input, msgCode, state)

	case ImpeachPreprepareMsgCode:
		// TODO: fix this, use correct impeach block verify function

		log.Debug("ImpeachHandler to call handleImpeachPreprepareMsg")

		return p.handleImpeachPreprepareMsg(input, state, func(block *types.Block) error {
			return p.dpor.ValidateBlock(block, false, true)
		})

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}

}

// ImpeachPrepareHandler is the handler for ImpeachPrepare state
func (p *LBFT2) ImpeachPrepareHandler(input *BlockOrHeader, msgCode MsgCode, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	switch msgCode {
	case ImpeachCommitMsgCode, ImpeachValidateMsgCode:

		log.Debug("ImpeachPrepareHandler to call ImpeachCommitHandler")

		return p.ImpeachCommitHandler(input, msgCode, state)

	case ImpeachPrepareMsgCode:

		log.Debug("ImpeachPrepareHandler to call handleImpeachPrepareMsg")

		return p.handleImpeachPrepareMsg(input, state)

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}

}

// ImpeachCommitHandler is the handler for ImpeachCommit state
func (p *LBFT2) ImpeachCommitHandler(input *BlockOrHeader, msgCode MsgCode, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {

	switch msgCode {
	case ImpeachValidateMsgCode:

		log.Debug("ImpeachCommitHandler to call handleImpeachValidateMsg")

		return p.handleImpeachValidateMsg(input, state)

	case ImpeachCommitMsgCode:

		log.Debug("ImpeachCommitHandler to call handleImpeachCommitMsg")

		return p.handleImpeachCommitMsg(input, state)

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}

}

// ValidateHandler is the handler for bot Validate state and ImpeachValidate state
func (p *LBFT2) ValidateHandler(input *BlockOrHeader, msgCode MsgCode, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	switch msgCode {
	case ValidateMsgCode:
		return p.handleValidateMsg(input, state)

	case ImpeachValidateMsgCode:
		return p.handleImpeachValidateMsg(input, state)

	default:
		return nil, NoAction, NoMsgCode, state, nil

	}
}

// fsm is a toy, not work now
func (p *LBFT2) fsm(input *BlockOrHeader, msgCode MsgCode, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	var (
		hash   = input.Hash()
		number = input.Number()
	)

	_, _ = hash, number

	// if already in chain, do nothing
	if p.dpor.HasBlockInChain(hash, number) {
		// TODO: add error type
		return nil, NoAction, NoMsgCode, state, nil
	}

	if number < p.Number() {
		log.Warn("outdated msg", "number", number, "hash", hash.Hex())
		// TODO: add error type
		return nil, NoAction, NoMsgCode, state, nil
	}

	// TODO: add state update function to avoid state reverse

	switch msgCode {
	case PreprepareMsgCode:
		return p.handlePreprepareMsg(input, state, func(block *types.Block) error {
			return p.dpor.ValidateBlock(block, false, true)
		})

	case PrepareMsgCode:
		return p.handlePrepareMsg(input, state)

	case CommitMsgCode:
		return p.handleCommitMsg(input, state)

	case ValidateMsgCode:
		return p.handleValidateMsg(input, state)

	case ImpeachPreprepareMsgCode:
		// TODO: fix this, use correct impeach block verify function
		return p.handleImpeachPreprepareMsg(input, state, func(block *types.Block) error {
			return p.dpor.ValidateBlock(block, false, true)
		})

	case ImpeachPrepareMsgCode:
		return p.handleImpeachPrepareMsg(input, state)

	case ImpeachCommitMsgCode:
		return p.handleImpeachCommitMsg(input, state)

	case ImpeachValidateMsgCode:
		return p.handleImpeachValidateMsg(input, state)

	default:

	}

	return nil, NoAction, NoMsgCode, state, nil
}

// prepareCertificate checks if prepare certificate is satisfied
func (p *LBFT2) prepareCertificate(bi BlockIdentifier) bool {
	return p.prepareSignatures.getSignaturesCountOf(bi) >= 2*int(p.Faulty())+1
}

// commitCertificate checks if commit certificate is satisfied
func (p *LBFT2) commitCertificate(bi BlockIdentifier) bool {
	return p.commitSignatures.getSignaturesCountOf(bi) >= 2*int(p.Faulty())+1
}

// impeachPrepareCertificate checks if impeach prepare certificate is satisfied
// TODO: it should be f+1, not 2f+1
func (p *LBFT2) impeachPrepareCertificate(bi BlockIdentifier) bool {
	return p.prepareCertificate(bi)
}

// impeachCommitCertificate checks if impeach commit certificate is satisfied
func (p *LBFT2) impeachCommitCertificate(bi BlockIdentifier) bool {
	return p.commitCertificate(bi)
}

// handlePreprepareMsg handles Preprepare msg
func (p *LBFT2) handlePreprepareMsg(input *BlockOrHeader, state consensus.State, blockVerifyFn VerifyBlockFn) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {

	// if input is not a block, return error
	if !input.IsBlock() {
		log.Warn("received a preprepare msg, but not a block", "number", input.Number(), "hash", input.Hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		number = input.Number()
		hash   = input.Hash()
		block  = input.block
	)

	log.Debug("received a preprepare block", "number", number, "hash", hash.Hex())

	// add the block to cache
	if err := p.blockCache.AddBlock(block); err != nil {
		log.Warn("failed to add the block to block cache", "number", number, "hash", hash.Hex())
		return nil, NoAction, NoMsgCode, state, err
	}

	log.Debug("ready to verify the block ", "number", number, "hash", hash.Hex())

	// verify the block
	switch err := blockVerifyFn(block); err {

	// the block is valid, sign it with prepare prefix
	case nil:

		log.Debug("verified the block, everything is ok! ready to sign the block", "number", number, "hash", hash.Hex())

		bi := NewBlockIdentifier(number, hash)

		// compose prepare msg
		prepareHeader, _ := p.composePrepareMsg(block)

		// if prepare certificate is satisfied
		if p.prepareCertificate(bi) {
			return p.oncePrepareCertificateSatisfied(prepareHeader)
		}

		// prepare certificate is not satisfied, broadcast prepare msg
		return []*BlockOrHeader{NewBOHFromHeader(prepareHeader)}, BroadcastMsgAction, PrepareMsgCode, consensus.Prepare, nil

	case consensus.ErrFutureBlock:

		log.Debug("verified the block, there is an error", "error", err)

		time.Sleep(100 * time.Millisecond)
		return p.handlePreprepareMsg(input, state, blockVerifyFn)

	case consensus.ErrUnknownAncestor:

		log.Debug("verified the block, there is an error", "error", err)

		time.Sleep(100 * time.Millisecond)
		go p.unknownAncestorBlockHandler(block)
		return p.handlePreprepareMsg(input, state, blockVerifyFn)

	default:

		log.Debug("verified the block, there is an error", "error", err)

	}

	return nil, NoAction, NoMsgCode, state, nil
}

// handleImpeachPreprepareMsg handles Impeach Preprepare msg
func (p *LBFT2) handleImpeachPreprepareMsg(input *BlockOrHeader, state consensus.State, blockVerifyFn VerifyImpeachBlockFn) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	if !input.IsBlock() {
		log.Warn("received an impeach preprepare msg, but not a block", "number", input.Number(), "hash", input.Hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		number = input.Number()
		hash   = input.Hash()
		block  = input.block
	)

	log.Debug("received an impeach preprepare block", "number", number, "hash", hash.Hex())

	// add the impeach block to cache
	if err := p.blockCache.AddBlock(block); err != nil {
		log.Warn("failed to add the block to block cache", "number", number, "hash", hash.Hex())
		return nil, NoAction, NoMsgCode, state, err
	}

	log.Debug("ready to verify the impeach block ", "number", number, "hash", hash.Hex())

	// verify the block
	switch err := blockVerifyFn(block); err {

	// the block is valid, sign it with prepare prefix
	case nil:

		log.Debug("verified the block, everything is ok! ready to sign the block", "number", number, "hash", hash.Hex())

		bi := NewBlockIdentifier(number, hash)

		// compose prepare msg
		impeachPrepareHeader, _ := p.composeImpeachPrepareMsg(block)

		// if prepare certificate is satisfied
		if p.impeachPrepareCertificate(bi) {
			return p.onceImpeachPrepareCertificateSatisfied(impeachPrepareHeader)
		}

		// prepare certificate is not satisfied, broadcast prepare msg
		return []*BlockOrHeader{NewBOHFromHeader(impeachPrepareHeader)}, BroadcastMsgAction, ImpeachPrepareMsgCode, consensus.ImpeachPrepare, nil

	case consensus.ErrFutureBlock:

		log.Debug("verified the block, there is an error", "error", err)

		time.Sleep(100 * time.Millisecond)
		return p.handleImpeachPreprepareMsg(input, state, blockVerifyFn)

	case consensus.ErrUnknownAncestor:

		log.Debug("verified the block, there is an error", "error", err)

		time.Sleep(100 * time.Millisecond)
		go p.unknownAncestorBlockHandler(block)
		return p.handleImpeachPreprepareMsg(input, state, blockVerifyFn)

	default:

		log.Debug("verified the block, there is an error", "error", err)

	}

	return nil, NoAction, NoMsgCode, state, nil
}

// composePrepareMsg composes a prepare msg for a given block
func (p *LBFT2) composePrepareMsg(block *types.Block) (*types.Header, error) {

	var (
		header = block.RefHeader()
		number = header.Number.Uint64()
		hash   = header.Hash()
	)

	// sign the header with prepare state prefix
	switch err := p.dpor.SignHeader(header, consensus.Prepare); err {
	case nil:

		_ = p.refreshSignatures(header, consensus.Prepare)

		log.Debug("succeed to sign the proposed block", "number", number, "hash", hash.Hex())

		return header, nil

	default:

		log.Warn("err when signing header", "number", number, "hash", hash.Hex(), "err", err)
		return header, err
	}
}

// composeImpeachPrepareMsg composes an impeach prepare msg for a given block
func (p *LBFT2) composeImpeachPrepareMsg(block *types.Block) (*types.Header, error) {
	var (
		header = block.RefHeader()
		number = header.Number.Uint64()
		hash   = header.Hash()
	)

	// sign the header with impeach prepare state prefix
	switch err := p.dpor.SignHeader(header, consensus.ImpeachPrepare); err {
	case nil:

		_ = p.refreshSignatures(header, consensus.ImpeachPrepare)

		log.Debug("succeed to sign the proposed impeach block", "number", number, "hash", hash.Hex())

		return header, nil

	default:

		log.Warn("err when signing header", "number", number, "hash", hash.Hex(), "err", err)
		return header, err
	}
}

// handlePrepareMsg handles Prepare msg
func (p *LBFT2) handlePrepareMsg(input *BlockOrHeader, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	// if the input is not a header, return error
	if !input.IsHeader() {
		log.Warn("received a prepare msg, but not a header", "number", input.Number(), "hash", input.Hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		number = input.Number()
		hash   = input.Hash()
		header = input.header
	)

	bi := NewBlockIdentifier(number, hash)

	log.Debug("received a prepare header", "number", number, "hash", hash.Hex())

	// refresh signatures in the header and local cache
	_ = p.refreshSignatures(header, consensus.Prepare)

	log.Debug("checking prepare certificate for the block", "number", number, "hash", hash.Hex())

	// if prepare certificate is satisfied
	if p.prepareCertificate(bi) {
		return p.oncePrepareCertificateSatisfied(header)
	}

	log.Debug("prepare certificate is not satisfied now, waiting...", "number", number, "hash", hash.Hex(), "count", p.prepareSignatures.getSignaturesCountOf(bi))

	return nil, NoAction, NoMsgCode, state, nil

}

// handleImpeachPrepareMsg handles Impeach Prepare msg
func (p *LBFT2) handleImpeachPrepareMsg(input *BlockOrHeader, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	// if the input is not a header, return error
	if !input.IsHeader() {
		log.Warn("received an impeach prepare msg, but not a header", "number", input.Number(), "hash", input.Hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		number = input.Number()
		hash   = input.Hash()
		header = input.header
	)

	bi := NewBlockIdentifier(number, hash)

	log.Debug("received an impeach prepare header", "number", number, "hash", hash.Hex())

	// refresh signatures in the header and local cache
	_ = p.refreshSignatures(header, consensus.ImpeachPrepare)

	log.Debug("checking impeach prepare certificate for the block", "number", number, "hash", hash.Hex())

	// if prepare certificate is satisfied
	if p.impeachPrepareCertificate(bi) {
		return p.onceImpeachPrepareCertificateSatisfied(header)
	}

	log.Debug("impeach prepare certificate is not satisfied now, waiting...", "number", number, "hash", hash.Hex(), "count", p.prepareSignatures.getSignaturesCountOf(bi))

	return nil, NoAction, NoMsgCode, state, nil

}

// composeCommitMsg composes a commit msg with given header
func (p *LBFT2) composeCommitMsg(h *types.Header) (*types.Header, error) {

	var (
		header = types.CopyHeader(h)
		number = header.Number.Uint64()
		hash   = header.Hash()
	)

	// prepare certificate is satisfied, sign the block with commit state
	switch err := p.dpor.SignHeader(header, consensus.Commit); err {
	case nil:

		// refresh signatures both in the header and local signatures cache
		_ = p.refreshSignatures(header, consensus.Commit)

		log.Debug("succeed to sign the header with commit state, broadcasting commit msg...", "number", number, "hash", hash.Hex())

		return header, nil

	default:

		log.Debug("failed to sign the header with commit state", "number", number, "hash", hash.Hex())
		return header, err
	}
}

// composeImpeachCommitMsg composes an impeach commit msg with given header
func (p *LBFT2) composeImpeachCommitMsg(h *types.Header) (*types.Header, error) {

	var (
		header = types.CopyHeader(h)
		number = header.Number.Uint64()
		hash   = header.Hash()
	)

	// impeach prepare certificate is satisfied, sign the block with impeach commit state
	switch err := p.dpor.SignHeader(header, consensus.ImpeachCommit); err {
	case nil:

		// refresh signatures both in the header and local signatures cache
		_ = p.refreshSignatures(header, consensus.ImpeachCommit)

		log.Debug("succeed to sign the header with impeach commit state, broadcasting impeach commit msg...", "number", number, "hash", hash.Hex())

		return header, nil

	default:

		log.Debug("failed to sign the header with impeach commit state", "number", number, "hash", hash.Hex())
		return header, err
	}
}

// handleCommitMsg handles Commit msg
func (p *LBFT2) handleCommitMsg(input *BlockOrHeader, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	// if the input is not a header, return error
	if !input.IsHeader() {
		log.Warn("received a commit msg, but not a header", "number", input.Number(), "hash", input.Hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		number = input.Number()
		hash   = input.Hash()
		header = input.header
	)

	bi := NewBlockIdentifier(number, hash)

	log.Debug("received a commit header", "number", number, "hash", hash.Hex())

	// refresh signatures both in cache and header
	err := p.refreshSignatures(header, consensus.Commit)
	if err != nil {
		log.Debug("error when refreshing signatures", "number", number, "hash", hash.Hex())
		return nil, NoAction, NoMsgCode, state, err
	}

	log.Debug("checking commit certificate for the block", "number", number, "hash", hash.Hex())

	// if enough commit sigs, broadcast it as validate msg
	if p.commitCertificate(bi) {
		return p.onceCommitCertificateSatisfied(nil, header)
	}

	log.Debug("commit certificate is not satisfied now, waiting...", "number", number, "hash", hash.Hex(), "count", p.commitSignatures.getSignaturesCountOf(bi))

	return nil, NoAction, NoMsgCode, state, err
}

// handleImpeachCommitMsg handles Impeach Commit msg
func (p *LBFT2) handleImpeachCommitMsg(input *BlockOrHeader, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	// if the input is not a header, return error
	if !input.IsHeader() {
		log.Warn("received an impeach commit msg, but not a header", "number", input.Number(), "hash", input.Hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		number = input.Number()
		hash   = input.Hash()
		header = input.header
	)

	bi := NewBlockIdentifier(number, hash)

	log.Debug("received an impeach commit header", "number", number, "hash", hash.Hex())

	// refresh signatures both in cache and header
	err := p.refreshSignatures(header, consensus.ImpeachCommit)
	if err != nil {
		log.Debug("error when refreshing signatures", "number", number, "hash", hash.Hex())
		return nil, NoAction, NoMsgCode, state, err
	}

	log.Debug("checking impeach commit certificate for the block", "number", number, "hash", hash.Hex())

	// if enough impeach commit sigs, broadcast it as validate msg
	if p.impeachCommitCertificate(bi) {
		return p.onceImpeachCommitCertificateSatisfied(nil, header)
	}

	log.Debug("impeach commit certificate is not satisfied now, waiting...", "number", number, "hash", hash.Hex(), "count", p.commitSignatures.getSignaturesCountOf(bi))

	return nil, NoAction, NoMsgCode, state, err
}

// composeValidateMsg composes a validate msg with given header
func (p *LBFT2) composeValidateMsg(header *types.Header) (*types.Block, error) {

	var (
		number = header.Number.Uint64()
		hash   = header.Hash()
	)

	bi := BlockIdentifier{
		hash:   hash,
		number: number,
	}

	// get block from local cache
	block, err := p.blockCache.GetBlock(bi)
	if err != nil {
		return nil, err
	}

	log.Debug("broadcasting the composed validate block to other validators...", "number", number, "hash", hash.Hex())

	return block.WithSeal(header), nil
}

// handleValidateMsg handles Validate msg
func (p *LBFT2) handleValidateMsg(input *BlockOrHeader, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	// if input is not a header, return error
	if !input.IsBlock() {
		log.Warn("received a validate msg, but not a block", "number", input.Number(), "hash", input.Hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		block = input.block
	)

	log.Debug("received a validate block", "number", block.NumberU64(), "hash", block.Hash().Hex())

	return []*BlockOrHeader{NewBOHFromBlock(block)}, BroadcastAndInsertBlockAction, ValidateMsgCode, consensus.Idle, nil
}

// handleImpeachValidateMsg handles Impeach Validate msg
func (p *LBFT2) handleImpeachValidateMsg(input *BlockOrHeader, state consensus.State) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {
	// if input is not a header, return error
	if !input.IsBlock() {
		log.Warn("received an impeach validate msg, but not a block", "number", input.Number(), "hash", input.Hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		block = input.block
	)

	log.Debug("received an impeach validate block", "number", block.NumberU64(), "hash", block.Hash().Hex())

	return []*BlockOrHeader{NewBOHFromBlock(block)}, BroadcastAndInsertBlockAction, ImpeachValidateMsgCode, consensus.Idle, nil
}

// refreshSignatures refreshes signatures in header and local cache
func (p *LBFT2) refreshSignatures(header *types.Header, state consensus.State) error {
	// recover validators and signatures in header
	signers, signatures, err := p.dpor.ECRecoverSigs(header, state)
	if err != nil {
		log.Debug("err when recovering signatures from header", "err", err, "state", state, "number", header.Number.Uint64(), "hash", header.Hash().Hex())
		return err
	}

	// get validators from dpor service
	validators, err := p.dpor.ValidatorsOf(header.Number.Uint64())
	if err != nil {
		log.Debug("err when getting validators of header", "err", err, "number", header.Number.Uint64(), "hash", header.Hash().Hex())
		return err
	}

	switch state {
	case consensus.Prepare, consensus.ImpeachPrepare:

		// cache signatures from header
		err = p.prepareSignatures.cacheSignaturesFromHeader(signers, signatures, validators, header)
		if err != nil {
			log.Debug("err when cache signatures from header with preprepared state", "err", err, "number", header.Number.Uint64(), "hash", header.Hash().Hex())
			return err
		}

		// write signatures from cache to header
		err = p.prepareSignatures.writeSignaturesToHeader(validators, header)
		if err != nil {
			log.Debug("err when write signatures to header with preprepared state", "err", err, "number", header.Number.Uint64(), "hash", header.Hash().Hex())
			return err
		}

	case consensus.Commit, consensus.ImpeachCommit:

		// cache signatures from header
		err = p.commitSignatures.cacheSignaturesFromHeader(signers, signatures, validators, header)
		if err != nil {
			log.Debug("err when cache signatures from header with prepared state", "err", err, "number", header.Number.Uint64(), "hash", header.Hash().Hex())
			return err
		}

		// write signatures from cache to header
		err = p.commitSignatures.writeSignaturesToHeader(validators, header)
		if err != nil {
			log.Debug("err when write signatures to header with prepared state", "err", err, "number", header.Number.Uint64(), "hash", header.Hash().Hex())
			return err
		}
	}

	return nil
}

// oncePrepareCertificateSatisfied returns msgs and actions once prepare certificate is satisfied
func (p *LBFT2) oncePrepareCertificateSatisfied(prepareHeader *types.Header) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {

	bi := BlockIdentifier{
		hash:   prepareHeader.Hash(),
		number: prepareHeader.Number.Uint64(),
	}

	// compose commit msg
	commitHeader := types.CopyHeader(prepareHeader)
	commitHeader, _ = p.composeCommitMsg(commitHeader)

	// if commit certificate is satisfied
	if p.commitCertificate(bi) {
		return p.onceCommitCertificateSatisfied(prepareHeader, commitHeader)
	}

	// commit certificate is not satisfied, broadcast prepare and commit msg
	return []*BlockOrHeader{NewBOHFromHeader(prepareHeader), NewBOHFromHeader(commitHeader)}, BroadcastMsgAction, PrepareAndCommitMsgCode, consensus.Commit, nil

}

// onceCommitCertificateSatisfied returns msgs and actions once commit certificate is satisfied
func (p *LBFT2) onceCommitCertificateSatisfied(prepareHeader *types.Header, commitHeader *types.Header) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {

	// compose validate msg
	block, err := p.composeValidateMsg(commitHeader)
	if err != nil {

		// failed to compose validate msg, broadcast prepare and commit msg
		if prepareHeader != nil {
			return []*BlockOrHeader{NewBOHFromHeader(prepareHeader), NewBOHFromHeader(commitHeader)}, BroadcastMsgAction, PrepareAndCommitMsgCode, consensus.Commit, nil
		}
		return []*BlockOrHeader{NewBOHFromHeader(commitHeader)}, BroadcastMsgAction, CommitMsgCode, consensus.Commit, nil
	}

	// succeed to compose validate msg, broadcast it
	return []*BlockOrHeader{NewBOHFromBlock(block)}, BroadcastMsgAction, ValidateMsgCode, consensus.Validate, nil

}

// onceImpeachPrepareCertificateSatisfied returns msgs and actions once impeach prepare certificate is satisfied
func (p *LBFT2) onceImpeachPrepareCertificateSatisfied(impeachPrepareHeader *types.Header) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {

	bi := BlockIdentifier{
		hash:   impeachPrepareHeader.Hash(),
		number: impeachPrepareHeader.Number.Uint64(),
	}

	// compose commit msg
	impeachCommitHeader := types.CopyHeader(impeachPrepareHeader)
	impeachCommitHeader, _ = p.composeImpeachCommitMsg(impeachCommitHeader)

	// if commit certificate is satisfied
	if p.impeachCommitCertificate(bi) {
		return p.onceImpeachCommitCertificateSatisfied(impeachPrepareHeader, impeachCommitHeader)
	}

	// commit certificate is not satisfied, broadcast prepare and commit msg
	return []*BlockOrHeader{NewBOHFromHeader(impeachPrepareHeader), NewBOHFromHeader(impeachCommitHeader)}, BroadcastMsgAction, ImpeachPrepareAndCommitMsgCode, consensus.ImpeachCommit, nil
}

// onceImpeachCommitCertificateSatisfied return msgs and actions once impeach commit certificate is satisfied
func (p *LBFT2) onceImpeachCommitCertificateSatisfied(impeachPrepareHeader *types.Header, impeachCommitHeader *types.Header) ([]*BlockOrHeader, Action, MsgCode, consensus.State, error) {

	// compose validate msg
	block, err := p.composeValidateMsg(impeachCommitHeader)
	if err != nil {
		// failed to compose validate msg, broadcast prepare and commit msg
		if impeachPrepareHeader != nil {
			return []*BlockOrHeader{NewBOHFromHeader(impeachPrepareHeader), NewBOHFromHeader(impeachCommitHeader)}, BroadcastMsgAction, ImpeachPrepareAndCommitMsgCode, consensus.ImpeachCommit, nil
		}

		return []*BlockOrHeader{NewBOHFromHeader(impeachCommitHeader)}, BroadcastMsgAction, ImpeachCommitMsgCode, consensus.ImpeachCommit, nil
	}

	// succeed to compose validate msg, broadcast it
	return []*BlockOrHeader{NewBOHFromBlock(block)}, BroadcastMsgAction, ImpeachValidateMsgCode, consensus.Validate, nil
}

// unknownAncestorBlockHandler handles unknown ancestor block
func (p *LBFT2) unknownAncestorBlockHandler(block *types.Block) {
	number := block.NumberU64()

	if number <= p.number {
		return
	}

	// recover proposer's address
	proposer, err := p.dpor.ECRecoverProposer(block.Header())
	if err != nil {
		return
	}

	// verify if a legit proposer
	term := p.dpor.TermOf(number)
	isP, err := p.dpor.VerifyProposerOf(proposer, term)
	if err != nil {
		return
	}

	// if legit, cache the block!
	if isP {
		if err := p.blockCache.AddBlock(block); err != nil {
			log.Warn("failed to add block to cache", "number", number, "hash", block.Hash().Hex(), "error", err)
		}
		return
	}

	// if term is larger than local, sync!
	if p.dpor.TermOf(number) > p.dpor.TermOf(p.number) {
		go p.dpor.Synchronise()
	}
}

// Impeachment waits until it is time to impeach, then try to compose an impeach block
type Impeachment struct {
	dpor      DporService
	returnFn  HandleGeneratedImpeachBlock
	restartCh chan struct{}
	numberCh  chan uint64
	quitCh    chan struct{}
	running   bool
	lock      sync.RWMutex
}

// NewImpeachment creates a new Impeachment struct
func NewImpeachment(dpor DporService, returnFn HandleGeneratedImpeachBlock) *Impeachment {
	return &Impeachment{
		dpor:      dpor,
		returnFn:  returnFn,
		restartCh: make(chan struct{}),
		numberCh:  make(chan uint64),
		quitCh:    make(chan struct{}),
	}
}

func (im *Impeachment) isRunning() bool {
	im.lock.RLock()
	defer im.lock.RUnlock()

	return im.running
}

func (im *Impeachment) setRunning(running bool) {
	im.lock.Lock()
	defer im.lock.Unlock()

	im.running = running
}

// number returns current block number in local chain + 1
func (im *Impeachment) number() uint64 {
	return im.dpor.Status().Head.Number.Uint64()
}

func (im *Impeachment) timeout() time.Duration {
	return im.dpor.ImpeachTimeout()
}

// waitAndComposeImpeachBlock waits timeout to impeach, or return
func (im *Impeachment) waitAndComposeImpeachBlock(number uint64) {
	if number <= im.number() {
		return
	}

	im.setRunning(true)
	defer im.setRunning(false)

	select {
	case <-time.After(im.timeout()):
		impeachBlock, err := im.dpor.CreateImpeachBlock()
		if err != nil {
			log.Warn("err when creating impeach block", "err", err)
			return
		}

		_ = im.returnFn(impeachBlock)
		return

	case <-im.restartCh:
		return
	}
}

// Trigger triggers an impeachment
func (im *Impeachment) Trigger(number uint64) {
	im.numberCh <- number
	log.Debug("triggered restart", "number", number)
}

// Restart restarts impeachment
func (im *Impeachment) Restart(number uint64) {
	if im.isRunning() {
		im.restartCh <- struct{}{}
	}

	log.Debug("now starting new wait and try to compose", "number", number)

	go im.waitAndComposeImpeachBlock(number)

}

// Loop loops for impeachment
func (im *Impeachment) Loop() {

	for {
		select {
		case number := <-im.numberCh:
			log.Debug("now ready to restart", "number", number)
			go im.Restart(number)
		case <-im.quitCh:
			return
		}
	}
}

// Stop stops impeachment
func (im *Impeachment) Stop() {
	im.quitCh <- struct{}{}
}
