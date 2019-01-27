package backend

import (
	"bytes"
	"errors"
	"fmt"
	"sync"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	lru "github.com/hashicorp/golang-lru"
)

const (
	MaxBlockCacheSize = 200
)

// Action is type enumerator for FSM action
type Action uint8

// BroadcastMultipleMsgAction is used for a rare case
// when both (impeach) prepare and commit messages are about to send out
const (
	NoAction Action = iota
	BroadcastMsgAction
	BroadcastMultipleMsgAction
	InsertBlockAction
	BroadcastAndInsertBlockAction
)

// DataType is type enumerator for FSM output
type DataType uint8

const (
	NoType DataType = iota
	HeaderType
	BlockType
)

// MsgCode is type enumerator for FSM message type
type MsgCode uint8

// NoMsgCode is a alias for nil
// PreprepareMsgCode indicates a newly proposed block
// PrepareAndCommitMsgCode is used when combing with BroadcastMultipleMsgAction
// ImpeachPrepareAndCommitMsgCode is also paired with BroadcastMultipleMsgAction
// If committed certificates is also collected, the validator only needs to broadcast a validate message
// It is because validate message will cover the functions of other messages
// There do not exist a scenario that broadcast both normal case and impeach message
// The rationale is that any validator enters an impeachment process cannot sent out a normal case message
const (
	NoMsgCode MsgCode = iota
	PreprepareMsgCode
	PrepareMsgCode
	CommitMsgCode
	PrepareAndCommitMsgCode
	ValidateMsgCode
	ImpeachPreprepareMsgCode
	ImpeachPrepareMsgCode
	ImpeachCommitMsgCode
	ImpeachPrepareAndCommitMsgCode
	ImpeachValidateMsgCode
)

var (
	ErrBlockTooOld                     = errors.New("the block is too old")
	ErrFsmWrongDataType                = errors.New("an unexpected FSM input data type")
	ErrFsmFaultyBlock                  = errors.New("the newly proposed block is faulty")
	ErrFsmWrongIdleInput               = errors.New("not a proper input for idle state")
	ErrFsmWrongPrepreparedInput        = errors.New("not a proper input for pre-prepared state")
	ErrFsmWrongPreparedInput           = errors.New("not a proper input for prepared state")
	ErrFsmWrongImpeachPrepreparedInput = errors.New("not a proper input for impeach pre-prepared state")
	ErrFsmWrongImpeachPreparedInput    = errors.New("not a proper input for impeach prepared state")
	ErrBlockNotExist                   = errors.New("the block does not exist")
	ErrBlockInvalid                    = errors.New("the block format is invalid")
	ErrProposeImpeachBlockFails        = errors.New("fails to propose impeach block")
)

// BlockSignature is a signature set of validators for a block with specific hash
type BlockSignature struct {
	hash      common.Hash         // the block's hash
	signature types.DporSignature // signature of the block
}

// Signature is for test purpose
func (bs *BlockSignature) Signature() types.DporSignature {
	return bs.signature
}

// SignaturesOfState address -> blockSigItem -> (hash, sig)
type SignaturesOfState map[common.Address]*BlockSignature

// DSMStatus represents a Dpor State Machine Status
type DSMStatus struct {
	Number uint64
	State  consensus.State
}

//DporStateMachine is a struct containing variables used for state transition in FSM
type DporStateMachine struct {
	state     consensus.State
	stateLock sync.RWMutex

	faulty uint64 // faulty is the parameter of 3f+1 nodes in Byzantine
	number uint64

	dpor       DporService
	blockCache *lru.ARCCache // cache of blocks

	prepareSignatures SignaturesOfState
	commitSignatures  SignaturesOfState
	signaturesLock    sync.RWMutex

	lock sync.RWMutex
}

// NewDSM creates a new dpor fsm
func NewDSM(faulty uint64, latest uint64, dpor DporService) *DporStateMachine {
	blockCache, _ := lru.NewARC(MaxBlockCacheSize)

	return &DporStateMachine{
		state:             consensus.Idle,
		dpor:              dpor,
		faulty:            faulty,
		number:            latest,
		blockCache:        blockCache,
		prepareSignatures: make(map[common.Address]*BlockSignature),
		commitSignatures:  make(map[common.Address]*BlockSignature),
	}
}

// Status retrieves status of dsm
func (dsm *DporStateMachine) Status() DSMStatus {
	return DSMStatus{
		Number: dsm.Number(),
		State:  dsm.State(),
	}
}

// Service is for test purpose
func (dsm *DporStateMachine) Service() DporService {
	return dsm.dpor
}

// State returns current dpor state
func (dsm *DporStateMachine) State() consensus.State {
	dsm.stateLock.RLock()
	defer dsm.stateLock.RUnlock()

	return dsm.state
}

// SetState sets dpor pbft state
func (dsm *DporStateMachine) SetState(state consensus.State) {
	dsm.stateLock.Lock()
	defer dsm.stateLock.Unlock()

	dsm.state = state
}

// Number returns current number
func (dsm *DporStateMachine) Number() uint64 {
	dsm.lock.RLock()
	defer dsm.lock.RUnlock()

	return dsm.number
}

// SetNumber sets dpor pbft number
func (dsm *DporStateMachine) SetNumber(number uint64) {
	dsm.lock.Lock()
	defer dsm.lock.Unlock()

	dsm.number = number
}

// PrepareSigState is for test purpose
func (dsm *DporStateMachine) PrepareSigState() SignaturesOfState {
	dsm.stateLock.RLock()
	defer dsm.stateLock.RUnlock()

	return dsm.prepareSignatures
}

// CommitSigState is for test purpose
func (dsm *DporStateMachine) CommitSigState() SignaturesOfState {
	dsm.stateLock.RLock()
	defer dsm.stateLock.RUnlock()

	return dsm.prepareSignatures
}

func (dsm *DporStateMachine) resetSignatureStates() {
	dsm.signaturesLock.Lock()
	defer dsm.signaturesLock.Unlock()

	dsm.prepareSignatures = make(map[common.Address]*BlockSignature)
	dsm.commitSignatures = make(map[common.Address]*BlockSignature)
}

// updateNumber resets a signature state for a renewed block number(height)
func (dsm *DporStateMachine) updateNumber(number uint64) {
	if number <= dsm.Number() {
		return
	}

	dsm.SetNumber(number)
	dsm.resetSignatureStates()
}

// verifyBlock is a func to verify whether the block is legal
func (dsm *DporStateMachine) verifyBlock(block *types.Block) bool {
	return dsm.dpor.ValidateBlock(block, false, true) == nil
}

//prepareCertificate is true if the validator has collects 2f+1 prepare messages
func (dsm *DporStateMachine) prepareCertificate(header *types.Header) bool {
	var (
		count = uint64(0)
		hash  = header.Hash()
	)

	for _, item := range dsm.prepareSignatures {
		if bytes.Equal(item.hash[:], hash[:]) {
			count++
		}
	}

	log.Debug("prepared certificate", "count", count)
	return count >= 2*dsm.faulty+1
}

// commitCertificate is true if the validator has collected 2f+1 commit messages
func (dsm *DporStateMachine) commitCertificate(header *types.Header) bool {
	var (
		count = uint64(0)
		hash  = header.Hash()
	)

	for _, item := range dsm.commitSignatures {
		if bytes.Equal(item.hash[:], hash[:]) {
			count++
		}
	}

	log.Debug("commit certificate", "count", count)
	return count >= 2*dsm.faulty+1
}

// Add one to the counter of prepare messages
func (dsm *DporStateMachine) updatePrepareSignatures(h *types.Header) error {

	dsm.updateNumber(h.Number.Uint64())

	// retrieve signers for checking
	signers, sigs, err := dsm.dpor.ECRecoverSigs(h, consensus.Prepare)
	if err != nil {
		log.Warn("failed to recover signatures of preparing phase", "error", err)
		return err
	}
	log.Debug("EcrecoverSigs: signers", "len(signers)", len(signers))

	// check the signers are validators
	validators, _ := dsm.dpor.ValidatorsOf(h.Number.Uint64())
	var checkErr error = nil
	for _, s := range signers {
		isValidator := false
		for _, v := range validators {
			if s == v {
				isValidator = true
			}
		}
		if !isValidator {
			log.Warn("a signer is not in validator committee", "signer", s.Hex())
			checkErr = consensus.ErrInvalidSigners
		}
	}
	if checkErr != nil {
		return checkErr
	}

	// some debug logs
	log.Debug("------------- prepareMsgPlus: display merging signatures to state (before state) BEGIN ---------------",
		"len(sm.prepareSigState)", len(dsm.prepareSignatures))
	idx := 0
	for k, v := range dsm.prepareSignatures {
		log.Debug(fmt.Sprintf("item #%d", idx), "signer", k.Hex(), "blockHash", v.hash.Hex(), "sig", common.Bytes2Hex(v.signature[:]))
		idx++
	}
	log.Debug("------------- prepareMsgPlus: END ---------------")

	// merge signatures to state
	hash := h.Hash()
	for i, s := range signers {
		// TODO: add lock here
		dsm.prepareSignatures[s] = &BlockSignature{
			hash:      hash,
			signature: sigs[i],
		}
	}

	// some debug logs
	log.Debug("------------- prepareMsgPlus: display merging signatures to state (after state) BEGIN ---------------",
		"len(sm.prepareSigState)", len(dsm.prepareSignatures))
	idx = 0
	for k, v := range dsm.prepareSignatures {
		log.Debug(fmt.Sprintf("item #%d", idx), "signer", k.Hex(), "blockHash", v.hash.Hex(), "sig", common.Bytes2Hex(v.signature[:]))
		idx++
	}
	log.Debug("------------- prepareMsgPlus: END ---------------")

	return nil
}

// updateCommitSignatures merge the signatures of commit messages
func (dsm *DporStateMachine) updateCommitSignatures(h *types.Header) error {

	dsm.updateNumber(h.Number.Uint64())

	// retrieve signers for checking
	signers, sigs, err := dsm.dpor.ECRecoverSigs(h, consensus.Commit)
	if err != nil {
		log.Warn("failed to recover signatures of committing phase", "error", err)
		return err
	}

	// check the signers are validators
	validators, _ := dsm.dpor.ValidatorsOf(h.Number.Uint64())
	var checkErr error = nil
	for _, s := range signers {
		isValidator := false
		for _, v := range validators {
			if s == v {
				isValidator = true
			}
		}
		if !isValidator {
			log.Warn("the signer is not in the validators committee", "signer", s.Hex())
			checkErr = consensus.ErrInvalidSigners
		}
	}
	if checkErr != nil {
		return checkErr
	}

	// some debug logs
	log.Debug("------------- commitMsgPlus: display merging signatures to state (before state) BEGIN ---------------",
		"len(prepareSigState)", len(dsm.prepareSignatures))
	idx := 0
	for k, v := range dsm.prepareSignatures {
		log.Debug(fmt.Sprintf("item #%d", idx), "signer", k.Hex(), "blockHash", v.hash.Hex(), "sig", common.Bytes2Hex(v.signature[:]))
		idx++
	}
	log.Debug("------------- commitMsgPlus: END ---------------")

	// merge signatures to state
	hash := h.Hash()
	for i, s := range signers {
		// TODO: add lock here
		dsm.commitSignatures[s] = &BlockSignature{
			hash:      hash,
			signature: sigs[i],
		}
	}

	// some debug logs
	log.Debug("------------- commitMsgPlus: display merging signatures to state (after state) BEGIN ---------------",
		"len(prepareSigState)", len(dsm.prepareSignatures))
	idx = 0
	for k, v := range dsm.prepareSignatures {
		log.Debug(fmt.Sprintf("item #%d", idx), "signer", k.Hex(), "blockHash", v.hash.Hex(), "sig", common.Bytes2Hex(v.signature[:]))
		idx++
	}
	log.Debug("------------- commitMsgPlus: END ---------------")

	return nil
}

// It is used to compose prepare message given a newly proposed block
func (dsm *DporStateMachine) composePrepareMsg(b *types.Block) (*types.Header, error) {
	// too old header
	if dsm.Number() > b.NumberU64() {
		return nil, ErrBlockTooOld
	}

	// update dsm status
	if dsm.Number() < b.NumberU64() {
		dsm.updateNumber(b.NumberU64())
		dsm.blockCache.Add(b.Hash(), b) // add to cache
	}

	// TODO: remove this later
	// update prepare signature cache
	for v, item := range dsm.prepareSignatures {
		dsm.dpor.UpdatePrepareSigsCache(v, item.hash, item.signature)
	}

	// sign the header with prepare state / preprepared
	dsm.dpor.SignHeader(b.RefHeader(), consensus.Prepare)

	log.Debug("sign block by validator at prepare msg", "blocknum", dsm.number, "sigs", b.RefHeader().Dpor.SigsFormatText())

	// update prepare signatures
	dsm.updatePrepareSignatures(b.Header())

	return b.Header(), nil
}

func (dsm *DporStateMachine) composeCommitMsg(h *types.Header) (*types.Header, error) {
	// too old header
	if dsm.Number() > h.Number.Uint64() {
		return nil, ErrBlockTooOld
	}

	// update dsm number
	dsm.updateNumber(h.Number.Uint64())

	// update commit signatures
	// TODO: remove this later
	for v, item := range dsm.commitSignatures {
		dsm.dpor.UpdateFinalSigsCache(v, item.hash, item.signature)
	}

	// sign the header with commit state / prepared
	dsm.dpor.SignHeader(h, consensus.Commit)

	log.Debug("sign block by validator at commit msg", "blocknum", dsm.number, "sigs", h.Dpor.SigsFormatText())

	// update commit signatures
	dsm.updateCommitSignatures(h)

	return h, nil
}

// composeValidateMsg is to return the validate message, which is the proposed block or impeach block
func (dsm *DporStateMachine) composeValidateMsg(header *types.Header) (block *types.Block, err error) {

	var (
		hash       = header.Hash()
		validators = header.Dpor.Validators
	)

	// retrieve the block from cache
	blk, ok := dsm.blockCache.Get(hash)
	// TODO: fix this, if fail to get the block from cache, broadcast a commit msg to other validators
	if !ok {
		log.Warn("failed to retrieve block from cache", "hash", hash, "number", header.Number.Uint64())
		return nil, ErrBlockNotExist
	}
	if block, ok = blk.(*types.Block); !ok {
		return nil, ErrBlockInvalid
	}

	// make up the all signatures if missing
	for i, v := range validators {
		if block.Dpor().Sigs[i].IsEmpty() { // if the sig is empty, try make up it
			// try to find the sig in cache
			state := dsm.commitSignatures[v]
			if state != nil && state.hash == hash { // if the validator signed the block, use its signature
				copy(block.Dpor().Sigs[i][:], state.signature[:])
			}
		}
	}

	return block, nil
}

// This function is used for add the block into the cache, if a validator (prepared state) receives a proposed block that not in the cache
func (dsm *DporStateMachine) addBlockCache(b *types.Block) error {
	hash := b.Hash()
	_, got := dsm.blockCache.Get(hash)
	if !got {
		dsm.updateNumber(b.NumberU64())
		dsm.blockCache.Add(b.Hash(), b) // add the impeach block into the cache
	}

	return nil
}

//It is used to propose an impeach block
func (dsm *DporStateMachine) proposeImpeachBlock() *types.Block {
	// create an impeach block
	impeachBlock, err := dsm.dpor.CreateImpeachBlock()
	if err != nil {
		log.Warn("creating impeachment block failed", "error", err)
		return nil
	}

	// update dsm number
	dsm.updateNumber(impeachBlock.NumberU64())

	// add the impeach block to cache
	dsm.blockCache.Add(impeachBlock.Hash(), impeachBlock) // add the impeach block into the cache

	// sign the header with impeach preprepared state
	// TODO: return an error
	dsm.dpor.SignHeader(impeachBlock.RefHeader(), consensus.ImpeachPrepare)

	log.Debug("proposed an impeachment block", "hash", impeachBlock.Hash().Hex(), "sigs", impeachBlock.Header().Dpor.SigsFormatText())

	// update impeach prepare signatures
	dsm.updateImpeachPrepareSignatures(impeachBlock.Header())

	return impeachBlock
}

func (dsm *DporStateMachine) impeachPreparedCertificate(h *types.Header) bool {
	return dsm.prepareCertificate(h)
}

func (dsm *DporStateMachine) updateImpeachPrepareSignatures(h *types.Header) error {
	return dsm.updatePrepareSignatures(h)
}

func (dsm *DporStateMachine) composeImpeachCommitMsg(h *types.Header) (*types.Header, error) {
	return dsm.composeCommitMsg(h)
}

func (dsm *DporStateMachine) impeachCommitCertificate(h *types.Header) bool {
	return dsm.commitCertificate(h)
}

func (dsm *DporStateMachine) updateImpeachCommitSignatures(h *types.Header) error {
	return dsm.updateCommitSignatures(h)
}

func (dsm *DporStateMachine) composeImpeachValidateMsg(h *types.Header) (*types.Block, error) {
	return dsm.composeValidateMsg(h)
}

// It is action when a validator receive a legal pre-prepare message in Idle state
func (dsm *DporStateMachine) composePrepareMsgAction(input interface{}, defaultState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	// TODO: change input to Block type
	inputBlock := input.(*types.Block)
	inputHeader := inputBlock.Header()

	// compose a prepare msg
	ret, err := dsm.composePrepareMsg(inputBlock)
	if err != nil {
		log.Warn("error when handling pre-prepareMsg on", defaultState, "state", "error", err)
		return nil, NoAction, NoType, NoMsgCode, defaultState, err
	}

	// test if prepare certificate is satisfied, if so, compose commit msg
	if dsm.prepareCertificate(inputHeader) {

		// compose commit msg
		ret2, err := dsm.composeCommitMsg(inputHeader)
		if err != nil {
			log.Warn("error when compose commit msg when sufficing a certificate")
			var output []interface{}
			output = append(output, ret)
			return output, BroadcastMsgAction, HeaderType, PrepareMsgCode, consensus.Prepare, err
		}

		// For a rare case that this newly composed commit message suffice a committed certificate in a cascade
		// It is about to send out both prepare and commit message if two certificates are collected

		// if commit certificate is satisfied, compose a validate msg
		if dsm.commitCertificate(inputHeader) {

			log.Debug("Collect a prepare certificate and a committed certificate in Idle state, stay in Idle state")

			// compose a validate msg
			b, err := dsm.composeValidateMsg(inputHeader)
			if err != nil {
				log.Warn("error when handling committed certificate while collecting prepared certificate, "+
					"convert to Prepared state", "error", err)
				var output []interface{}
				output = append(output, ret)
				output = append(output, ret2)
				return output, BroadcastMultipleMsgAction, HeaderType, PrepareAndCommitMsgCode, consensus.Commit, nil
			}

			// return the composed validate msg
			log.Debug("Collect a committed certificate in Idle state, stay in Idle state")
			var output []interface{}
			output = append(output, b)
			return output, BroadcastAndInsertBlockAction, BlockType, ValidateMsgCode, consensus.Idle, err
		}

		// return the composed commit msg
		log.Debug("Collect a prepared certificate in Idle state, convert to Prepared state")
		var output []interface{}
		output = append(output, ret)
		output = append(output, ret2)
		return output, BroadcastMultipleMsgAction, HeaderType, PrepareAndCommitMsgCode, consensus.Commit, nil
	}

	// return the composed prepare msg
	log.Debug("Receive a pre-prepare message in Idle state, transit to pre-prepared state")
	var output []interface{}
	output = append(output, ret)
	return output, BroadcastMsgAction, HeaderType, PrepareMsgCode, consensus.Prepare, nil
}

func (dsm *DporStateMachine) proposeImpeachBlockAction(input interface{}, defaultState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	// TODO: change this input to Block type
	// Test if its impeach prepared and committed certificate has been sufficed
	b := input.(*types.Block)
	inputHeader := b.Header()

	// if impeach prepare certificate is satisfied, compose impeach commit msg
	if dsm.impeachPreparedCertificate(inputHeader) {

		// compose impeach commit msg
		ret2, err := dsm.composeImpeachCommitMsg(inputHeader)
		if err != nil {
			var output []interface{}
			output = append(output, b.Header())
			log.Warn("error when composing an impeach commit message")
			return output, BroadcastMsgAction, HeaderType, ImpeachPrepareMsgCode, consensus.ImpeachPrepare, err
		}

		// if impeach commit msg is satisfied, compose validate msg
		if dsm.impeachCommitCertificate(inputHeader) {

			// compose impeach validate msg
			b2, err := dsm.composeImpeachValidateMsg(inputHeader)
			if err != nil {
				log.Debug("Receive a faulty pre-prepare message, transit to impeach pre-prepared state")
				log.Warn("error when handling impeachPrepareMsg", "error", err)
				var output []interface{}
				output = append(output, b.Header())
				output = append(output, ret2)
				return output, BroadcastMultipleMsgAction, HeaderType, ImpeachPrepareAndCommitMsgCode, consensus.ImpeachCommit, nil

			}

			// return the composed impeach validate msg
			log.Debug("Collect an impeach committed certificate")
			var output []interface{}
			output = append(output, b2)
			return output, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
		}

		// return the composed impeach commit msg
		log.Debug("Collect an impeach prepared certificate, transit to impeach prepared state")
		var output []interface{}
		output = append(output, b.Header())
		output = append(output, ret2)
		return output, BroadcastMultipleMsgAction, HeaderType, ImpeachPrepareAndCommitMsgCode, consensus.ImpeachCommit, nil
	}

	// return the composed impeach prepare msg
	log.Debug("Receive a pre-prepare message, transit to impeach pre-prepared state")
	var output []interface{}
	output = append(output, b.Header())
	return output, BroadcastMsgAction, HeaderType, ImpeachPrepareMsgCode, defaultState, nil
}

func (dsm *DporStateMachine) composeCommitMsgAction(input interface{}, defaultState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	// TODO: change this input to Header type
	inputHeader := input.(*types.Header)

	// compose commit msg
	ret, err := dsm.composeCommitMsg(inputHeader)
	if err != nil {
		return nil, NoAction, NoType, NoMsgCode, defaultState, err
	}

	// For a rare case that newly composed commit message suffice a committed certificate

	// if commit certificate is satisfied, compose a validate msg
	if dsm.commitCertificate(inputHeader) {

		log.Debug("Collect a prepare certificate and a committed certificate in", defaultState, "state, convert to Idle state")

		// compose validate msg
		b, err := dsm.composeValidateMsg(inputHeader)
		if err != nil {
			log.Warn("error when handling committed certificate while collecting prepared certificate, "+
				"convert to Prepared state", "error", err)
			var output []interface{}
			output = append(output, ret)
			return output, BroadcastMsgAction, HeaderType, CommitMsgCode, consensus.Commit, nil
		}

		// return the composed validate msg
		log.Debug("Collect a committed certificate in", defaultState, "state, stay in Idle state")
		var output []interface{}
		output = append(output, b)
		return output, BroadcastAndInsertBlockAction, BlockType, ValidateMsgCode, consensus.Idle, err

	}

	// return the composed prepare msg
	log.Debug("Collect a prepared certificate in", defaultState, "state, convert to Prepared state")
	var output []interface{}
	output = append(output, ret)
	return output, BroadcastMsgAction, HeaderType, CommitMsgCode, consensus.Commit, nil
}

func (dsm *DporStateMachine) composeImpeachCommitMsgAction(input interface{}, defaultState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	// TODO: change this input to Header type
	inputHeader := input.(*types.Header)

	// compose impeach commit msg
	ret, err := dsm.composeImpeachCommitMsg(inputHeader)
	if err != nil {
		log.Warn("error when composing an impeach commit message")
		return nil, NoAction, NoType, NoMsgCode, defaultState, err
	}

	// check if it further suffices an impeach committed certificate in a cascade

	// if impeach commit certificate is satisfied, compose a validate msg
	if dsm.impeachCommitCertificate(inputHeader) {

		// compose the validate msg
		b, err := dsm.composeImpeachValidateMsg(inputHeader)
		if err != nil {
			log.Warn("error when handling impeachCommitMsg on", defaultState, "state", "error", err)
			var output []interface{}
			output = append(output, ret)
			return output, BroadcastMsgAction, HeaderType, ImpeachCommitMsgCode, consensus.ImpeachCommit, err
		}

		// return the validate msg
		log.Debug("Collect an impeach committed certificate in", defaultState, "state, stay in Idle state")
		var output []interface{}
		output = append(output, b)
		return output, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
	}

	// return the impeach commit msg
	log.Debug("Collect an impeach prepared certificate in", defaultState, "state, transit to impeach prepared state")
	var output []interface{}
	output = append(output, ret)
	return output, BroadcastMsgAction, HeaderType, ImpeachCommitMsgCode, consensus.ImpeachCommit, nil
}

// FSM is the finite state machine for a validator, to output the correct state given on current state and inputs
// input is either a header or a block, referring to message or proposed (impeach) block
// inputType indicates the type of input
// msg indicates what type of message or block input is
// state is the current state of the validator
// the output interface is the message or block validator should handle
// the output action refers to what the validator should do with the output interface
// the output dataType indicates whether the output interface is block or header
// the output msgCode represents the type the output block or message
// the output consensus.State indicates the validator's next state
func (dsm *DporStateMachine) FSM(input interface{}, inputType DataType, msg MsgCode) ([]interface{}, Action, DataType, MsgCode, error) {
	state := dsm.State()

	log.Debug("state machine input", "data type", inputType, "msg code", msg, "state", state)

	output, act, dtype, msg, state, err := dsm.fsm(input, inputType, msg, state)

	log.Debug("state machine result", "action", act, "data type", dtype, "msg code", msg, "state", state, "err", err)

	dsm.SetState(state)

	return output, act, dtype, msg, nil
}

// Fsm is deprecated
func (dsm *DporStateMachine) Fsm(input interface{}, inputType DataType, msg MsgCode) (interface{}, Action, DataType, MsgCode, error) {

	output, act, dtype, msg, _ := dsm.FSM(input, inputType, msg)

	// err is not returned back
	// determine whether output is an nil slice of interface
	if output != nil {
		// if true, return the first element
		return output[0], act, dtype, msg, nil
	} else {
		// otherwise return a nil interface
		return nil, act, dtype, msg, nil
	}
}

// TODO: The output interface may need to revised as []interface{}, since multiple messages can be sent out
func (dsm *DporStateMachine) fsm(input interface{}, inputType DataType, msg MsgCode, currentState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	var header *types.Header
	var inputBlock *types.Block
	var err error

	// Determine the input is a header or a block by inputType
	switch inputType {
	case HeaderType:
		header = input.(*types.Header)
	case BlockType:
		inputBlock = input.(*types.Block)
	// If input == nil and inputType == noType, it means the the timer of validator expires
	case NoType:
		if input != nil {
			err = ErrFsmWrongDataType
		}
	default:
		log.Warn("Unexpected input and its data types")
		err = ErrFsmWrongDataType
		return nil, NoAction, NoType, NoMsgCode, currentState, err
	}

	switch currentState {
	// The case of consensus.Idle state
	case consensus.Idle:
		switch msg {
		// Stay in consensus.Idle state if receives validate message, and we should insert the block
		case ValidateMsgCode:
			return dsm.handleValidateMsg(inputBlock, currentState)

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case CommitMsgCode:
			return dsm.handleCommitMsg(header, currentState)

		// Jump to consensus.Prepared state if receive 2f+1 prepare message
		case PrepareMsgCode:
			return dsm.handlePrepareMsg(header, currentState)

		// For the case that receive the newly proposes block or pre-prepare message
		case PreprepareMsgCode:
			return dsm.handlePreprepareMsg(inputBlock, currentState)

		// Stay in consensus.Idle state and insert an impeachment block when receiving an impeach validate message
		case ImpeachValidateMsgCode:
			return dsm.handleValidateMsg(inputBlock, currentState)

		// Stay in consensus.Idle state if the validator collects 2f+1 impeach commit messages
		case ImpeachCommitMsgCode:
			return dsm.handleImpeachCommitMsg(header, currentState)

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case ImpeachPrepareMsgCode:
			return dsm.handleImpeachPrepareMsg(header, currentState)

		// Transit to impeach pre-prepared state if the timers expires (receiving an impeach pre-prepared message),
		// then generate the impeachment block and broadcast the impeach prepare massage
		case ImpeachPreprepareMsgCode:
			return dsm.handleImpeachPreprepareMsg(currentState)

		default:
			log.Warn("unexpected input for Idle state")
			err = ErrFsmWrongIdleInput
		}

	// The case of pre-prepared state
	case consensus.Prepare:
		switch msg {
		// Jump to committed state if receive a validate message
		case ValidateMsgCode:
			return dsm.handleValidateMsg(inputBlock, currentState)

		// Jump to committed state if receive 2f+1 commit messages
		case CommitMsgCode:
			return dsm.handleCommitMsg(header, currentState)

		// Convert to consensus.Prepared state if collect prepared certificate
		case PrepareMsgCode:
			return dsm.handlePrepareMsg(header, currentState)

		case ImpeachValidateMsgCode:
			return dsm.handleValidateMsg(inputBlock, currentState)

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case ImpeachCommitMsgCode:
			return dsm.handleImpeachCommitMsg(header, currentState)

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case ImpeachPrepareMsgCode:
			return dsm.handleImpeachPrepareMsg(header, currentState)

		// when the timer expires, the validator is about to propose an impeachment block
		case ImpeachPreprepareMsgCode:
			return dsm.handleImpeachPreprepareMsg(currentState)

		default:
			log.Warn("unexpected input for pre-prepared state")
			err = ErrFsmWrongPrepreparedInput
		}

	// The case of consensus.Prepared stage
	case consensus.Commit:
		switch msg {
		// Jump to committed state if receive a validate message
		case ValidateMsgCode:
			return dsm.handleValidateMsg(inputBlock, currentState)

		// convert to committed state if collects committed certificate
		case CommitMsgCode:
			return dsm.handleCommitMsg(header, currentState)

		// Transit to consensus.Idle state to insert impeach block
		case ImpeachValidateMsgCode:
			return dsm.handleValidateMsg(inputBlock, currentState)

		// Transit to consensus.Idle state to committed state if receive 2f+1 commit messages
		case ImpeachCommitMsgCode:
			return dsm.handleImpeachCommitMsg(header, currentState)

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case ImpeachPrepareMsgCode:
			return dsm.handleImpeachPrepareMsg(header, currentState)

		// when the timer expires, the validator is about to propose an impeachment block
		case ImpeachPreprepareMsgCode:
			return dsm.handleImpeachPreprepareMsg(currentState)

		// If the validator in prepared state has not received the block, check its verification and add its to the cache
		case PreprepareMsgCode:
			if dsm.prepareCertificate(inputBlock.Header()) {
				dsm.addBlockCache(inputBlock)
			}

		default:
			log.Warn("unexpected input for prepared state", "msg", msg)
			err = ErrFsmWrongPreparedInput

		}

	case consensus.ImpeachPrepare:
		switch msg {
		// Transit to consensus.Idle state when receiving impeach validate message
		case ImpeachValidateMsgCode:
			return dsm.handleValidateMsg(inputBlock, currentState)

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case ImpeachCommitMsgCode:
			return dsm.handleImpeachCommitMsg(header, currentState)

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case ImpeachPrepareMsgCode:
			return dsm.handleImpeachPrepareMsg(header, currentState)

		// Do nothing if receives multiple impeach prepared
		case ImpeachPreprepareMsgCode:
			log.Debug("Receives an impeach pre-prepare message in impeach pre-prepared state, do nothing")
			return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachCommit, nil
		default:
			log.Debug("unexpected input for impeach pre-prepared state, do nothing")
			err = ErrFsmWrongImpeachPrepreparedInput
		}

	case consensus.ImpeachCommit:
		switch msg {
		// Transit to consensus.Idle state when receiving impeach validate message
		case ImpeachValidateMsgCode:
			return dsm.handleValidateMsg(inputBlock, currentState)

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case ImpeachCommitMsgCode:
			return dsm.handleImpeachCommitMsg(header, currentState)

		case ImpeachPreprepareMsgCode:
			return dsm.handleImpeachPreprepareMsg(currentState)

		default:
			log.Warn("unexpected input for impeach prepared state")
			err = ErrFsmWrongImpeachPreparedInput
		}
	}

	// Do nothing if the validator receive an unexpected unexpected info
	return nil, NoAction, NoType, NoMsgCode, currentState, err
}

func (dsm *DporStateMachine) handleValidateMsg(block *types.Block, currentState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	log.Debug("Receive a validate message in state", "state", currentState)

	// verify the block, if invalid, return error
	err := dsm.dpor.ValidateBlock(block, true, true)
	if err != nil {
		log.Warn("received invalid validate block msg", "number", block.NumberU64(), "hash", block.Hash().Hex())
		return nil, NoAction, NoType, NoMsgCode, currentState, err
	}

	// the block is valid, return insert block action and idle state
	var output []interface{}
	output = append(output, block)
	return output, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil
}

func (dsm *DporStateMachine) handleCommitMsg(header *types.Header, currentState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	// update commit signatures
	err := dsm.updateCommitSignatures(header)
	if err != nil {
		log.Warn("error when handling commitMsg on Idle state", "error", err)
		return nil, NoAction, NoType, NoMsgCode, currentState, err
	}

	// if commit certificate is satisfied, compose validate msg
	if dsm.commitCertificate(header) {
		// compose a validate block msg
		block, err := dsm.composeValidateMsg(header)
		if err != nil {
			log.Warn("error when handling commitMsg on Idle state", "error", err)
			return nil, NoAction, NoType, NoMsgCode, currentState, err
		}

		// return the validate block msg
		log.Debug("Collect a committed certificate in Idle state, stay in Idle state")
		var output []interface{}
		output = append(output, block)
		return output, BroadcastAndInsertBlockAction, BlockType, ValidateMsgCode, consensus.Idle, nil
	}

	// return none action and nil error
	log.Debug("Receive a commit message in Idle state, stay in Idle state")
	return nil, NoAction, NoType, NoMsgCode, currentState, nil
}

func (dsm *DporStateMachine) handlePrepareMsg(header *types.Header, currentState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	// update prepare signatures
	err := dsm.updatePrepareSignatures(header)
	if err != nil {
		log.Warn("error when handling prepareMsg on Idle state", "error", err)
		return nil, NoAction, NoType, NoMsgCode, currentState, err
	}

	// if prepare certificate is satisfied, compose commit msg
	if dsm.prepareCertificate(header) {
		return dsm.composeCommitMsgAction(header, consensus.Commit)
	}

	// return none action and nil error
	log.Debug("receive a prepare message in Idle state, stay in Idle state")
	return nil, NoAction, NoType, NoMsgCode, currentState, nil
}

// TODO: fix this
func (dsm *DporStateMachine) handlePreprepareMsg(block *types.Block, currentState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {

	// Verify the newly proposed block is faulty or not, if valid, compose a prepare msg
	if dsm.verifyBlock(block) {
		// composePrepareMsgAction is going to compose a prepare msg
		// the default state Idle is due to the case composition fails
		// It further checks both certificates, forwards to corresponding state if a certificate is collected.
		return dsm.composePrepareMsgAction(block, consensus.Idle)
	}

	// TODO: return multi err for verifyBlock, only if invalid block for a right proposer, do impeachment
	// If it is faulty, activate impeachment process
	impeachBlock := dsm.proposeImpeachBlock()
	if impeachBlock != nil {
		// the default option is that it enters impeach pre-prepared phase
		// checks both impeach certificates, forwards to the corresponding state if it meets the condition
		return dsm.proposeImpeachBlockAction(impeachBlock, consensus.ImpeachPrepare)
	}

	// failed to impeach
	log.Warn("Receive a faulty pre-prepare message in Idle state, failed to propose an impeach block")
	return nil, NoAction, NoType, NoMsgCode, consensus.Idle, ErrProposeImpeachBlockFails
}

func (dsm *DporStateMachine) handleImpeachCommitMsg(header *types.Header, currentState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	// update impeach commit signatures
	err := dsm.updateImpeachCommitSignatures(header)
	if err != nil {
		log.Warn("error when handling impeachCommitMsg on Preprepared state", "error", err)
		return nil, NoAction, NoType, NoMsgCode, currentState, err
	}

	// if impeach commit certificate is satisfied, compose impeach validate msg
	if dsm.impeachCommitCertificate(header) {

		// compose impeach validate msg
		b, err := dsm.composeImpeachValidateMsg(header)
		if err != nil {
			log.Warn("error when handling impeachCommitMsg on Preprepared state", "error", err)
			return nil, NoAction, NoType, NoMsgCode, currentState, err
		}

		// return composed impeach block
		log.Debug("Collect an impeach committed certificate in Pre-prepared state, transit to Idle state")
		var output []interface{}
		output = append(output, b)
		return output, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
	}

	// return none action and preprepared state
	log.Debug("Receive an impeach commit message in Pre-prepared state, stay in Pre-prepare state")
	return nil, NoAction, NoType, NoMsgCode, currentState, nil
}

func (dsm *DporStateMachine) handleImpeachPrepareMsg(header *types.Header, currentState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	// update impeach prepare signatures
	err := dsm.updateImpeachPrepareSignatures(header)
	if err != nil {
		log.Warn("error when handling impeachPrepareMsg on Idle state", "error", err)
		return nil, NoAction, NoType, NoMsgCode, currentState, err
	}

	// if impeach prepare certificate is satisfied, compose an impeach commit msg
	if dsm.impeachPreparedCertificate(header) {
		return dsm.composeImpeachCommitMsgAction(header, currentState)
	}

	// return none action and idle state
	log.Debug("Receive an impeach prepare message in Idle state, stay in Idle state")
	return nil, NoAction, NoType, NoMsgCode, currentState, nil
}

func (dsm *DporStateMachine) handleImpeachPreprepareMsg(currentState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {

	// compose an impeach block
	impeachBlock := dsm.proposeImpeachBlock()
	if impeachBlock != nil {
		log.Debug("Receive an impeach pre-prepare message in Pre-prepared state, transit to impeach pre-prepared state")
		// the default option is that it enters impeach pre-prepared phase
		// checks both impeach certificates, forwards to the corresponding state if it meets the condition
		return dsm.proposeImpeachBlockAction(impeachBlock, consensus.ImpeachPrepare)
	}

	// failed to compose impeach block
	log.Warn("error when proposing impeach block")
	return nil, NoAction, NoType, NoMsgCode, currentState, ErrProposeImpeachBlockFails
}
