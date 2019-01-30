/*
this is LBFT 2.0
*/

package backend

import (
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	lru "github.com/hashicorp/golang-lru"
)

type blockOrHeader struct {
	block  *types.Block
	header *types.Header
}

func newBOHFromHeader(header *types.Header) *blockOrHeader {
	return &blockOrHeader{
		header: header,
	}
}

func newBOHFromBlock(block *types.Block) *blockOrHeader {
	return &blockOrHeader{
		block: block,
	}
}

func (bh *blockOrHeader) isBlock() bool {
	return bh != nil && bh.block != nil
}

func (bh *blockOrHeader) isHeader() bool {
	return bh != nil && bh.header != nil
}

func (bh *blockOrHeader) number() uint64 {
	if bh.isBlock() {
		return bh.block.NumberU64()
	} else if bh.isHeader() {
		return bh.header.Number.Uint64()
	}
	return uint64(0)
}

func (bh *blockOrHeader) hash() common.Hash {
	if bh.isBlock() {
		return bh.block.Hash()
	} else if bh.isHeader() {
		return bh.header.Hash()
	}
	return common.Hash{}
}

type signaturesOfBlock struct {
	signatures map[common.Address]types.DporSignature
	lock       sync.RWMutex
}

func newSignaturesOfBlock() *signaturesOfBlock {
	return &signaturesOfBlock{
		signatures: make(map[common.Address]types.DporSignature),
	}
}

func (sb *signaturesOfBlock) setSignature(signer common.Address, signature types.DporSignature) {
	sb.lock.Lock()
	defer sb.lock.Unlock()

	sb.signatures[signer] = signature
}

func (sb *signaturesOfBlock) getSignature(signer common.Address) (types.DporSignature, bool) {
	sb.lock.RLock()
	defer sb.lock.RUnlock()

	signature, ok := sb.signatures[signer]
	return signature, ok
}

func (sb *signaturesOfBlock) count() int {
	sb.lock.RLock()
	defer sb.lock.RUnlock()

	for signer := range sb.signatures {
		log.Debug("", "signer", signer.Hex())
	}

	return len(sb.signatures)
}

type signaturesForBlockCaches struct {
	signaturesForBlocks *lru.ARCCache
	lock                sync.RWMutex
}

func newSignaturesForBlockCaches() *signaturesForBlockCaches {
	sigCaches, _ := lru.NewARC(100)
	return &signaturesForBlockCaches{
		signaturesForBlocks: sigCaches,
	}
}

// getSignaturesCountOf returns the number of signatures for given block identifier
func (sc *signaturesForBlockCaches) getSignaturesCountOf(bi blockIdentifier) int {
	sc.lock.RLock()
	defer sc.lock.RUnlock()

	sigs, ok := sc.signaturesForBlocks.Get(bi)
	if sigs != nil && ok {

		log.Debug("counting signatures of block", "number", bi.number, "hash", bi.hash.Hex())

		return sigs.(*signaturesOfBlock).count()
	}

	return 0
}

// addSignatureFor adds a signature to signature caches
func (sc *signaturesForBlockCaches) addSignatureFor(bi blockIdentifier, signer common.Address, signature types.DporSignature) {
	sc.lock.Lock()
	defer sc.lock.Unlock()

	signatures := newSignaturesOfBlock()
	sigs, ok := sc.signaturesForBlocks.Get(bi)
	if sigs != nil && ok {
		signatures = sigs.(*signaturesOfBlock)
	}

	signatures.setSignature(signer, signature)
	sc.signaturesForBlocks.Add(bi, signatures)
}

func (sc *signaturesForBlockCaches) getSignatureFor(bi blockIdentifier, signer common.Address) (types.DporSignature, bool) {
	sc.lock.RLock()
	defer sc.lock.RUnlock()

	sigs, ok := sc.signaturesForBlocks.Get(bi)
	if sigs != nil && ok {
		return sigs.(*signaturesOfBlock).getSignature(signer)
	}
	return types.DporSignature{}, false
}

func (sc *signaturesForBlockCaches) cacheSignaturesFromHeader(signers []common.Address, signatures []types.DporSignature, validators []common.Address, header *types.Header) error {
	bi := blockIdentifier{
		hash:   header.Hash(),
		number: header.Number.Uint64(),
	}

	for i, s := range signers {
		isV := false
		for _, v := range validators {
			if s == v {
				isV = true
			}
		}
		if isV {
			sc.addSignatureFor(bi, s, signatures[i])
		}
	}

	return nil
}

func (sc *signaturesForBlockCaches) writeSignaturesToHeader(validators []common.Address, header *types.Header) error {
	bi := blockIdentifier{
		hash:   header.Hash(),
		number: header.Number.Uint64(),
	}

	for i, v := range validators {
		if signature, ok := sc.getSignatureFor(bi, v); ok {
			header.Dpor.Sigs[i] = signature
		}
	}

	return nil
}

// PBFT is a state machine used for consensus protocol for validators msg processing
type PBFT struct {
	state     consensus.State
	stateLock sync.RWMutex

	faulty uint64 // faulty is the parameter of 3f+1 nodes in Byzantine
	lock   sync.RWMutex

	dpor       DporService
	blockCache *RecentBlocks // cache of blocks

	prepareSignatures *signaturesForBlockCaches
	commitSignatures  *signaturesForBlockCaches
}

func NewPBFT(faulty uint64, dpor DporService, handleImpeachBlock HandleGeneratedImpeachBlock) *PBFT {

	pbft := &PBFT{
		state:  consensus.Idle,
		faulty: faulty,
		dpor:   dpor,

		blockCache:        newKnownBlocks(),
		prepareSignatures: newSignaturesForBlockCaches(),
		commitSignatures:  newSignaturesForBlockCaches(),
	}

	return pbft
}

// Faulty returns the number of faulty nodes
func (p *PBFT) Faulty() uint64 {
	p.lock.RLock()
	defer p.lock.RUnlock()

	return p.faulty
}

// State returns current state
func (p *PBFT) State() consensus.State {
	p.stateLock.RLock()
	defer p.stateLock.RUnlock()

	return p.state
}

// SetState sets state of the state machine
func (p *PBFT) SetState(state consensus.State) {
	p.stateLock.Lock()
	defer p.stateLock.Unlock()

	p.state = state
}

// Number returns current number
func (p *PBFT) Number() uint64 {

	return p.dpor.GetCurrentBlock().NumberU64() + 1
}

// Status returns current states
func (p *PBFT) Status() DSMStatus {
	return DSMStatus{
		State:  p.State(),
		Number: p.Number(),
	}
}

// FSM implements ConsensusStateMachine.FSM
func (p *PBFT) FSM(input *blockOrHeader, msgCode MsgCode) ([]*blockOrHeader, Action, MsgCode, error) {

	state := p.State()

	output, action, msgCode, state, err := p.realFSM(input, msgCode, state)
	// output, action, msgCode, state, err := p.fsm(input, msgCode, state)

	if err == nil {
		p.SetState(state)
	}

	return output, action, msgCode, err
}

func (p *PBFT) realFSM(input *blockOrHeader, msgCode MsgCode, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	var (
		hash   = input.hash()
		number = input.number()
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

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}

}

func (p *PBFT) IdleHandler(input *blockOrHeader, msgCode MsgCode, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	switch msgCode {
	case ImpeachPreprepareMsgCode, ImpeachPrepareMsgCode, ImpeachCommitMsgCode, ImpeachValidateMsgCode:
		return p.ImpeachHandler(input, msgCode, state)

	case PrepareMsgCode, CommitMsgCode, ValidateMsgCode:
		return p.PrepareHandler(input, msgCode, state)

	case PreprepareMsgCode:
		return p.handlePreprepareMsg(input, state, func(block *types.Block) error {
			return p.dpor.ValidateBlock(block, false, true)
		})

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}
}

func (p *PBFT) PrepareHandler(input *blockOrHeader, msgCode MsgCode, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	switch msgCode {
	case ImpeachPreprepareMsgCode, ImpeachPrepareMsgCode, ImpeachCommitMsgCode, ImpeachValidateMsgCode:
		return p.ImpeachHandler(input, msgCode, state)

	case CommitMsgCode, ValidateMsgCode:
		return p.CommitHandler(input, msgCode, state)

	case PrepareMsgCode:
		return p.handlePrepareMsg(input, state)

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}
}

func (p *PBFT) CommitHandler(input *blockOrHeader, msgCode MsgCode, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	switch msgCode {
	case ImpeachPreprepareMsgCode, ImpeachPrepareMsgCode, ImpeachCommitMsgCode, ImpeachValidateMsgCode:
		return p.ImpeachHandler(input, msgCode, state)

	case ValidateMsgCode:
		return p.handleValidateMsg(input, state)

	case CommitMsgCode:
		return p.handleCommitMsg(input, state)

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}
}

func (p *PBFT) ImpeachHandler(input *blockOrHeader, msgCode MsgCode, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	switch msgCode {
	case ImpeachPrepareMsgCode, ImpeachCommitMsgCode, ImpeachValidateMsgCode:
		return p.ImpeachPrepareHandler(input, msgCode, state)

	case ImpeachPreprepareMsgCode:
		// TODO: fix this, use correct impeach block verify function
		return p.handleImpeachPreprepareMsg(input, state, func(block *types.Block) error {
			return p.dpor.ValidateBlock(block, false, true)
		})

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}

}

func (p *PBFT) ImpeachPrepareHandler(input *blockOrHeader, msgCode MsgCode, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	switch msgCode {
	case ImpeachCommitMsgCode, ImpeachValidateMsgCode:
		return p.ImpeachCommitHandler(input, msgCode, state)

	case ImpeachPrepareMsgCode:
		return p.handleImpeachPrepareMsg(input, state)

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}

}

func (p *PBFT) ImpeachCommitHandler(input *blockOrHeader, msgCode MsgCode, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {

	switch msgCode {
	case ImpeachValidateMsgCode:
		return p.handleImpeachValidateMsg(input, state)

	case ImpeachCommitMsgCode:
		return p.handleImpeachCommitMsg(input, state)

	default:
		return nil, NoAction, NoMsgCode, state, nil
	}

}

func (p *PBFT) fsm(input *blockOrHeader, msgCode MsgCode, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	var (
		hash   = input.hash()
		number = input.number()
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

func (p *PBFT) prepareCertificate(bi blockIdentifier) bool {
	return p.prepareSignatures.getSignaturesCountOf(bi) >= 2*int(p.Faulty())+1
}

func (p *PBFT) impeachPrepareCertificate(bi blockIdentifier) bool {
	return p.prepareCertificate(bi)
}

func (p *PBFT) commitCertificate(bi blockIdentifier) bool {
	return p.commitSignatures.getSignaturesCountOf(bi) >= 2*int(p.Faulty())+1
}

func (p *PBFT) impeachCommitCertificate(bi blockIdentifier) bool {
	return p.commitCertificate(bi)
}

func (p *PBFT) handlePreprepareMsg(input *blockOrHeader, state consensus.State, blockVerifyFn VerifyBlockFn) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {

	// if input is not a block, return error
	if !input.isBlock() {
		log.Warn("received a preprepare msg, but not a block", "number", input.number(), "hash", input.hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		number = input.number()
		hash   = input.hash()
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

		bi := blockIdentifier{
			hash:   hash,
			number: number,
		}

		// compose prepare msg
		prepareHeader, _ := p.composePrepareMsg(block)

		// if prepare certificate is satisfied
		if p.prepareCertificate(bi) {
			return p.oncePrepareCertificateSatisfied(prepareHeader)
		}

		// prepare certificate is not satisfied, broadcast prepare msg
		return []*blockOrHeader{newBOHFromHeader(prepareHeader)}, BroadcastMsgAction, PrepareMsgCode, consensus.Prepare, nil

	// the block is a future block, just wait a second.
	case consensus.ErrFutureBlock:

		log.Debug("verified the block, there is an error", "error", err)

		time.Sleep(1 * time.Second)
		return p.handlePreprepareMsg(input, state, blockVerifyFn)

	// same as future block
	case consensus.ErrUnknownAncestor:

		log.Debug("verified the block, there is an error", "error", err)

		time.Sleep(1 * time.Second)
		return p.handlePreprepareMsg(input, state, blockVerifyFn)

	default:

		log.Debug("verified the block, there is an error", "error", err)

	}

	return nil, NoAction, NoMsgCode, state, nil
}

func (p *PBFT) handleImpeachPreprepareMsg(input *blockOrHeader, state consensus.State, blockVerifyFn VerifyImpeachBlockFn) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	if !input.isBlock() {
		log.Warn("received an impeach preprepare msg, but not a block", "number", input.number(), "hash", input.hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		number = input.number()
		hash   = input.hash()
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

		bi := blockIdentifier{
			hash:   hash,
			number: number,
		}

		// compose prepare msg
		impeachPrepareHeader, _ := p.composeImpeachPrepareMsg(block)

		// if prepare certificate is satisfied
		if p.impeachPrepareCertificate(bi) {
			return p.onceImpeachPrepareCertificateSatisfied(impeachPrepareHeader)
		}

		// prepare certificate is not satisfied, broadcast prepare msg
		return []*blockOrHeader{newBOHFromHeader(impeachPrepareHeader)}, BroadcastMsgAction, ImpeachPrepareMsgCode, consensus.ImpeachPrepare, nil

	// the block is a future block, just wait a second.
	case consensus.ErrFutureBlock:

		log.Debug("verified the block, there is an error", "error", err)

		time.Sleep(1 * time.Second)
		return p.handleImpeachPreprepareMsg(input, state, blockVerifyFn)

	// same as future block
	case consensus.ErrUnknownAncestor:

		log.Debug("verified the block, there is an error", "error", err)

		time.Sleep(1 * time.Second)
		return p.handleImpeachPreprepareMsg(input, state, blockVerifyFn)

	default:

		log.Debug("verified the block, there is an error", "error", err)

	}

	return nil, NoAction, NoMsgCode, state, nil
}

func (p *PBFT) composePrepareMsg(block *types.Block) (*types.Header, error) {

	var (
		header = block.RefHeader()
		number = header.Number.Uint64()
		hash   = header.Hash()
	)

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

func (p *PBFT) composeImpeachPrepareMsg(block *types.Block) (*types.Header, error) {
	var (
		header = block.RefHeader()
		number = header.Number.Uint64()
		hash   = header.Hash()
	)

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

func (p *PBFT) handlePrepareMsg(input *blockOrHeader, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	// if the input is not a header, return error
	if !input.isHeader() {
		log.Warn("received a prepare msg, but not a header", "number", input.number(), "hash", input.hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		number = input.number()
		hash   = input.hash()
		header = input.header
	)

	bi := blockIdentifier{
		hash:   hash,
		number: number,
	}

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

func (p *PBFT) handleImpeachPrepareMsg(input *blockOrHeader, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	// if the input is not a header, return error
	if !input.isHeader() {
		log.Warn("received an impeach prepare msg, but not a header", "number", input.number(), "hash", input.hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		number = input.number()
		hash   = input.hash()
		header = input.header
	)

	bi := blockIdentifier{
		hash:   hash,
		number: number,
	}

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

func (p *PBFT) composeCommitMsg(h *types.Header) (*types.Header, error) {

	var (
		header = types.CopyHeader(h)
		number = header.Number.Uint64()
		hash   = header.Hash()
	)

	// prepare certificate is satisfied, sign the block with prepared(commit) state
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

func (p *PBFT) composeImpeachCommitMsg(h *types.Header) (*types.Header, error) {

	var (
		header = types.CopyHeader(h)
		number = header.Number.Uint64()
		hash   = header.Hash()
	)

	// impeach prepare certificate is satisfied, sign the block with impeach prepared(impeach commit) state
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

func (p *PBFT) handleCommitMsg(input *blockOrHeader, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	// if the input is not a header, return error
	if !input.isHeader() {
		log.Warn("received a commit msg, but not a header", "number", input.number(), "hash", input.hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		number = input.number()
		hash   = input.hash()
		header = input.header
	)

	bi := blockIdentifier{
		hash:   hash,
		number: number,
	}

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

func (p *PBFT) handleImpeachCommitMsg(input *blockOrHeader, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	// if the input is not a header, return error
	if !input.isHeader() {
		log.Warn("received an impeach commit msg, but not a header", "number", input.number(), "hash", input.hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		number = input.number()
		hash   = input.hash()
		header = input.header
	)

	bi := blockIdentifier{
		hash:   hash,
		number: number,
	}

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

func (p *PBFT) composeValidateMsg(header *types.Header) (*types.Block, error) {

	var (
		number = header.Number.Uint64()
		hash   = header.Hash()
	)

	bi := blockIdentifier{
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

func (p *PBFT) handleValidateMsg(input *blockOrHeader, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	// if input is not a header, return error
	if !input.isBlock() {
		log.Warn("received a validate msg, but not a block", "number", input.number(), "hash", input.hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		block = input.block
	)

	log.Debug("received a validate block", "number", block.NumberU64(), "hash", block.Hash().Hex())

	return []*blockOrHeader{newBOHFromBlock(block)}, BroadcastAndInsertBlockAction, ValidateMsgCode, consensus.Idle, nil
}

func (p *PBFT) handleImpeachValidateMsg(input *blockOrHeader, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	// if input is not a header, return error
	if !input.isBlock() {
		log.Warn("received an impeach validate msg, but not a block", "number", input.number(), "hash", input.hash().Hex())
		// TODO: return useful error
		return nil, NoAction, NoMsgCode, state, nil
	}

	var (
		block = input.block
	)

	log.Debug("received an impeach validate block", "number", block.NumberU64(), "hash", block.Hash().Hex())

	return []*blockOrHeader{newBOHFromBlock(block)}, BroadcastAndInsertBlockAction, ImpeachValidateMsgCode, consensus.Idle, nil
}

// refreshSignatures refreshes signatures in header and local cache
func (p *PBFT) refreshSignatures(header *types.Header, state consensus.State) error {
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

func (p *PBFT) onceImpeachPrepareCertificateSatisfied(impeachPrepareHeader *types.Header) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {

	bi := blockIdentifier{
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
	return []*blockOrHeader{newBOHFromHeader(impeachPrepareHeader), newBOHFromHeader(impeachCommitHeader)}, BroadcastMsgAction, ImpeachPrepareAndCommitMsgCode, consensus.ImpeachCommit, nil
}

func (p *PBFT) onceImpeachCommitCertificateSatisfied(impeachPrepareHeader *types.Header, impeachCommitHeader *types.Header) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {

	// compose validate msg
	block, err := p.composeValidateMsg(impeachCommitHeader)
	if err != nil {
		// failed to compose validate msg, broadcast prepare and commit msg
		if impeachPrepareHeader != nil {
			return []*blockOrHeader{newBOHFromHeader(impeachPrepareHeader), newBOHFromHeader(impeachCommitHeader)}, BroadcastMsgAction, ImpeachPrepareAndCommitMsgCode, consensus.ImpeachCommit, nil
		}

		return []*blockOrHeader{newBOHFromHeader(impeachCommitHeader)}, BroadcastMsgAction, ImpeachCommitMsgCode, consensus.ImpeachCommit, nil
	}

	// succeed to compose validate msg, broadcast it
	return []*blockOrHeader{newBOHFromBlock(block)}, BroadcastMsgAction, ImpeachValidateMsgCode, consensus.Idle, nil
}

func (p *PBFT) oncePrepareCertificateSatisfied(prepareHeader *types.Header) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {

	bi := blockIdentifier{
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
	return []*blockOrHeader{newBOHFromHeader(prepareHeader), newBOHFromHeader(commitHeader)}, BroadcastMsgAction, PrepareAndCommitMsgCode, consensus.Commit, nil

}

func (p *PBFT) onceCommitCertificateSatisfied(prepareHeader *types.Header, commitHeader *types.Header) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {

	// compose validate msg
	block, err := p.composeValidateMsg(commitHeader)
	if err != nil {

		// failed to compose validate msg, broadcast prepare and commit msg
		if prepareHeader != nil {
			return []*blockOrHeader{newBOHFromHeader(prepareHeader), newBOHFromHeader(commitHeader)}, BroadcastMsgAction, PrepareAndCommitMsgCode, consensus.Commit, nil
		}
		return []*blockOrHeader{newBOHFromHeader(commitHeader)}, BroadcastMsgAction, CommitMsgCode, consensus.Commit, nil
	}

	// succeed to compose validate msg, broadcast it
	return []*blockOrHeader{newBOHFromBlock(block)}, BroadcastMsgAction, ValidateMsgCode, consensus.Idle, nil

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

func (im *Impeachment) Stop() {
	im.quitCh <- struct{}{}
}
