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
	number uint64
	lock   sync.RWMutex

	dpor       DporService
	blockCache *RecentBlocks // cache of blocks

	prepareSignatures *signaturesForBlockCaches
	commitSignatures  *signaturesForBlockCaches
}

func NewPBFT(faulty uint64, number uint64, dpor DporService) *PBFT {

	return &PBFT{
		state:  consensus.Idle,
		faulty: faulty,
		number: number,
		dpor:   dpor,

		blockCache:        newKnownBlocks(),
		prepareSignatures: newSignaturesForBlockCaches(),
		commitSignatures:  newSignaturesForBlockCaches(),
	}
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
	p.lock.RLock()
	defer p.lock.RUnlock()

	return p.number
}

// SetNumber sets number for current view
func (p *PBFT) SetNumber(number uint64) {
	p.lock.Lock()
	defer p.lock.Unlock()

	p.number = number
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

	output, action, msgCode, state, err := p.fsm(input, msgCode, state)

	p.SetState(state)
	if len(output) != 0 {
		p.SetNumber(output[0].number())
	}

	return output, action, msgCode, err
}

func (p *PBFT) fsm(input *blockOrHeader, msgCode MsgCode, state consensus.State) ([]*blockOrHeader, Action, MsgCode, consensus.State, error) {
	var (
		hash   = input.hash()
		number = input.number()
	)

	_, _ = hash, number

	// if already in chain, do nothing
	if p.dpor.HasBlockInChain(hash, number) {
		log.Warn("the block or header is already in local chain", "number", number, "hash", hash.Hex())
		return nil, NoAction, NoMsgCode, state, nil
	}

	// TODO: add state update function to avoid state reverse

	// switch state {
	// case consensus.Idle:

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

	default:

	}

	// case consensus.Preprepared:

	// 	switch msgCode {
	// 	case PreprepareMsgCode:

	// 		log.Warn("received preprepare msg in preprepared state", "number", number, "hash", hash.Hex(), "fsm.number", p.Number(), "fsm.state", p.State())

	// 	case PrepareMsgCode:
	// 		return p.handlePrepareMsg(input, state)

	// 	case CommitMsgCode:
	// 		return p.handleCommitMsg(input, state)

	// 	case ValidateMsgCode:
	// 		return p.handleValidateMsg(input, state)

	// 	default:

	// 	}

	// case consensus.Prepared:

	// 	switch msgCode {
	// 	case PreprepareMsgCode:

	// 		log.Warn("received preprepare msg in prepared state", "number", number, "hash", hash.Hex(), "fsm.number", p.Number(), "fsm.state", p.State())

	// 	case PrepareMsgCode:

	// 		log.Warn("received prepare msg in prepared state", "number", number, "hash", hash.Hex(), "fsm.number", p.Number(), "fsm.state", p.State())

	// 	case CommitMsgCode:
	// 		return p.handleCommitMsg(input, state)

	// 	case ValidateMsgCode:
	// 		return p.handleValidateMsg(input, state)

	// 	default:

	// 	}

	// default:
	// }

	return nil, NoAction, NoMsgCode, state, nil
}

func (p *PBFT) prepareCertificate(bi blockIdentifier) bool {
	return p.prepareSignatures.getSignaturesCountOf(bi) >= 2*int(p.Faulty())+1
}

func (p *PBFT) commitCertificate(bi blockIdentifier) bool {
	return p.commitSignatures.getSignaturesCountOf(bi) >= 2*int(p.Faulty())+1
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
		header = input.block.RefHeader()
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

		// compose prepare msg
		header, _ = p.composePrepareMsg(block)

		return []*blockOrHeader{newBOHFromHeader(header)}, BroadcastMsgAction, PrepareMsgCode, consensus.Preprepared, nil

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

func (p *PBFT) composePrepareMsg(block *types.Block) (*types.Header, error) {

	var (
		header = block.RefHeader()
		number = header.Number.Uint64()
		hash   = header.Hash()
	)

	switch err := p.dpor.SignHeader(header, consensus.Preprepared); err {
	case nil:

		_ = p.refreshSignatures(header, consensus.Preprepared)

		log.Debug("succeed to sign the proposed block", "number", number, "hash", hash.Hex())

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
	_ = p.refreshSignatures(header, consensus.Preprepared)

	log.Debug("checking prepare certificate for the block", "number", number, "hash", hash.Hex())

	// if enough prepare sigs, sign it as commit msg
	if p.prepareCertificate(bi) {

		log.Debug("prepare certificate is satisfied, signing it with commit state", "number", number, "hash", hash.Hex())

		// prepare certificate is satisfied, sign the block with prepared(commit) state
		// compose commit msg
		prepareHeader := types.CopyHeader(header)
		header, _ = p.composeCommitMsg(header)

		return []*blockOrHeader{newBOHFromHeader(prepareHeader), newBOHFromHeader(header)}, BroadcastMsgAction, PrepareAndCommitMsgCode, consensus.Prepared, nil
		// return []*blockOrHeader{newBOHFromHeader(header)}, BroadcastMsgAction, CommitMsgCode, consensus.Prepared, nil

	}

	log.Debug("prepare certificate is not satisfied now, waiting...", "number", number, "hash", hash.Hex(), "count", p.prepareSignatures.getSignaturesCountOf(bi))

	return nil, NoAction, NoMsgCode, state, nil

}

func (p *PBFT) composeCommitMsg(h *types.Header) (*types.Header, error) {

	var (
		header = types.CopyHeader(h)
		number = header.Number.Uint64()
		hash   = header.Hash()
	)

	// prepare certificate is satisfied, sign the block with prepared(commit) state
	switch err := p.dpor.SignHeader(header, consensus.Prepared); err {
	case nil:

		// refresh signatures both in the header and local signatures cache
		_ = p.refreshSignatures(header, consensus.Prepared)

		log.Debug("succeed to sign the header with commit state, broadcasting commit msg...", "number", number, "hash", hash.Hex())

		return header, nil

	default:

		log.Debug("failed to sign the header with commit state", "number", number, "hash", hash.Hex())
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
	err := p.refreshSignatures(header, consensus.Prepared)
	if err != nil {
		log.Debug("error when refreshing signatures", "number", number, "hash", hash.Hex())
		return nil, NoAction, NoMsgCode, state, err
	}

	log.Debug("checking commit certificate for the block", "number", number, "hash", hash.Hex())

	// if enough commit sigs, broadcast it as validate msg
	if p.commitCertificate(bi) {

		log.Debug("commit certificate is satisfied, retrieving the block from cache", "number", number, "hash", hash.Hex())

		// compose validate msg
		block, err := p.composeValidateMsg(header)
		if err != nil {
			log.Warn("err when get block from cache", "err", err, "number", number)

			// failed to compose validate msg, broadcast commit msg
			return []*blockOrHeader{newBOHFromHeader(header)}, BroadcastMsgAction, CommitMsgCode, consensus.Prepared, nil
		}

		log.Debug("broadcasting the composed validate block to other validators...", "number", number, "hash", hash.Hex())

		// succeed to compose validate msg, broadcast it!
		return []*blockOrHeader{newBOHFromBlock(block)}, BroadcastMsgAction, ValidateMsgCode, consensus.Idle, nil

	}

	log.Debug("commit certificate is not satisfied now, waiting...", "number", number, "hash", hash.Hex(), "count", p.commitSignatures.getSignaturesCountOf(bi))

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

	log.Debug("inserting into local chain", "number", block.NumberU64(), "hash", block.Hash().Hex())

	// insert into chain
	err := p.dpor.InsertChain(block)
	if err != nil {
		log.Debug("failed to insert the block to local chain", "number", block.NumberU64(), "hash", block.Hash().Hex())
		return nil, NoAction, NoMsgCode, state, err
	}

	log.Debug("inserted into local chain, broadcasting to civilian...", "number", block.NumberU64(), "hash", block.Hash().Hex())

	// broadcast it to civilians
	go p.dpor.BroadcastBlock(block, true)

	return nil, NoAction, NoMsgCode, consensus.Idle, nil
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
	case consensus.Preprepared:

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

	case consensus.Prepared:

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
