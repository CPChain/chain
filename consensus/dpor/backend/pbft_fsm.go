package backend

import (
	"bytes"
	"errors"
	"fmt"
	"sync"

	_ "net/http/pprof"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	lru "github.com/hashicorp/golang-lru"
)

//Type enumerator for FSM action
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

//Type enumerator for FSM output
type DataType uint8

const (
	NoType DataType = iota
	HeaderType
	BlockType
)

//Type enumerator for FSM message type
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
	ErrProposeImpeachBlockFails        = errors.New("fails to propose impeach block")
)

// address -> blockSigItem -> (hash, sig)
type SigState map[common.Address]*BlockSigItem

type BlockSigItem struct {
	hash common.Hash         // the block's hash
	sig  types.DporSignature // signature of the block
}

const CacheSize = 200

//DporStateMachine is a struct containing variables used for state transition in FSM
type DporStateMachine struct {
	lock      sync.RWMutex
	state     consensus.State
	stateLock sync.RWMutex

	service         DporService
	prepareSigState SigState
	commitSigState  SigState
	f               uint64        // f is the parameter of 3f+1 nodes in Byzantine
	bcache          *lru.ARCCache // block cache
	lastHeight      uint64
}

func NewDporStateMachine(service DporService, f uint64) *DporStateMachine {
	bc, _ := lru.NewARC(CacheSize)

	return &DporStateMachine{
		state:           consensus.Idle,
		service:         service,
		prepareSigState: make(map[common.Address]*BlockSigItem),
		commitSigState:  make(map[common.Address]*BlockSigItem),
		f:               f,
		bcache:          bc,
		lastHeight:      0,
	}
}

// Sig is for test purpose
func (bsi *BlockSigItem) Sig() types.DporSignature {
	return bsi.sig
}

// Service is for test purpose
func (dsm *DporStateMachine) Service() DporService {
	return dsm.service
}

// PrepareSigState is for test purpose
func (dsm *DporStateMachine) PrepareSigState() SigState {
	dsm.stateLock.RLock()
	defer dsm.stateLock.RUnlock()

	return dsm.prepareSigState
}

// CommitSigState is for test purpose
func (dsm *DporStateMachine) CommitSigState() SigState {
	dsm.stateLock.RLock()
	defer dsm.stateLock.RUnlock()

	return dsm.prepareSigState
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

// refreshWhenNewerHeight resets a signature state for a renewed block number(height)
func (dsm *DporStateMachine) refreshWhenNewerHeight(height uint64) {
	dsm.lock.Lock()
	defer dsm.lock.Unlock()

	if height > dsm.lastHeight {
		dsm.lastHeight = height
		dsm.prepareSigState = make(map[common.Address]*BlockSigItem)
		dsm.commitSigState = make(map[common.Address]*BlockSigItem)
	}
}

// verifyBlock is a func to verify whether the block is legal
func (dsm *DporStateMachine) verifyBlock(block *types.Block) bool {
	dsm.lock.RLock()
	defer dsm.lock.RUnlock()

	return dsm.service.ValidateBlock(block, false, true) == nil
}

// committedCertificate is true if the validator has collected 2f+1 commit messages
func (dsm *DporStateMachine) committedCertificate(h *types.Header) bool {
	dsm.lock.RLock()
	defer dsm.lock.RUnlock()

	hash := h.Hash()
	var count uint64 = 0
	for _, item := range dsm.commitSigState {
		log.Debug("committedCertificate: compare hash", "hash", hash.Hex(), "sigHash", item.hash.Hex())
		if bytes.Equal(item.hash[:], hash[:]) {
			// TODO: @AC it had better to check whether the signature is valid for safety, consider add the check in future
			count++
		}
	}

	log.Debug("committed certificate", "count", count)
	return count >= 2*dsm.f+1
}

// composeValidateMsg is to return the validate message, which is the proposed block or impeach block
func (dsm *DporStateMachine) composeValidateMsg(h *types.Header) (*types.Block, error) {
	dsm.lock.RLock()
	defer dsm.lock.RUnlock()

	hash := h.Hash()
	b, got := dsm.bcache.Get(hash)
	if !got {
		log.Warn("failed to retrieve block from cache", "hash", hash)
		return nil, ErrBlockNotExist
	}
	blk := b.(*types.Block)

	// make up the all signatures if missing
	validators := h.Dpor.Validators
	for i, v := range validators {
		if blk.Dpor().Sigs[i].IsEmpty() { // if the sig is empty, try make up it
			// try to find the sig in cache
			state := dsm.commitSigState[v]
			// fmt.Println("composeValidateMsg state:", state)
			if state != nil && state.hash == hash { // if the validator signed the block, use its signature
				copy(blk.Dpor().Sigs[i][:], state.sig[:])
			}
		}
	}

	return blk, nil
}

// commitMsgPlus merge the signatures of commit messages
func (dsm *DporStateMachine) commitMsgPlus(h *types.Header) error {

	dsm.refreshWhenNewerHeight(h.Number.Uint64())

	// retrieve signers for checking
	signers, sigs, err := dsm.service.EcrecoverSigs(h, consensus.Prepared)
	if err != nil {
		log.Warn("failed to recover signatures of committing phase", "error", err)
		return err
	}

	// check the signers are validators
	validators, _ := dsm.service.ValidatorsOf(h.Number.Uint64())
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

	dsm.lock.Lock()

	log.Debug("------------- commitMsgPlus: display merging signatures to state (before state) BEGIN ---------------",
		"len(prepareSigState)", len(dsm.prepareSigState))
	idx := 0
	for k, v := range dsm.prepareSigState {
		log.Debug(fmt.Sprintf("item #%d", idx), "signer", k.Hex(), "blockHash", v.hash.Hex(), "sig", common.Bytes2Hex(v.sig[:]))
		idx++
	}
	log.Debug("------------- commitMsgPlus: END ---------------")

	// merge signature to state
	hash := h.Hash()
	for i, s := range signers {
		dsm.commitSigState[s] = &BlockSigItem{
			hash: hash,
			sig:  sigs[i],
		}
	}

	log.Debug("------------- commitMsgPlus: display merging signatures to state (after state) BEGIN ---------------",
		"len(prepareSigState)", len(dsm.prepareSigState))
	idx = 0
	for k, v := range dsm.prepareSigState {
		log.Debug(fmt.Sprintf("item #%d", idx), "signer", k.Hex(), "blockHash", v.hash.Hex(), "sig", common.Bytes2Hex(v.sig[:]))
		idx++
	}
	log.Debug("------------- commitMsgPlus: END ---------------")

	dsm.lock.Unlock()

	return nil
}

func (dsm *DporStateMachine) composeCommitMsg(h *types.Header) (*types.Header, error) {
	// TODO: add lock here
	if dsm.lastHeight > h.Number.Uint64() {
		return nil, ErrBlockTooOld
	}

	dsm.refreshWhenNewerHeight(h.Number.Uint64())

	// validator signs the block, update final sigs cache first
	for v, item := range dsm.commitSigState {
		dsm.service.UpdateFinalSigsCache(v, item.hash, item.sig)
	}
	dsm.service.SignHeader(h, consensus.Prepared)
	log.Info("sign block by validator at commit msg", "blocknum", dsm.lastHeight, "sigs", h.Dpor.SigsFormatText())

	// add itself
	dsm.commitMsgPlus(h)

	return h, nil
}

//preparedCertificate is true if the validator has collects 2f+1 prepare messages
func (dsm *DporStateMachine) preparedCertificate(h *types.Header) bool {
	dsm.lock.RLock()
	defer dsm.lock.RUnlock()

	hash := h.Hash()
	var count uint64 = 0
	fmt.Println("len(dsm.prepareSigState), dsm.prepareSigState:", len(dsm.prepareSigState), dsm.prepareSigState)
	for _, item := range dsm.prepareSigState {
		if bytes.Equal(item.hash[:], hash[:]) {
			// TODO: @AC it had better to check whether the signature is valid for safety, consider add the check in future
			log.Debug("preparedCertificate: compare hash", "hash", hash.Hex(), "sigHash", item.hash.Hex())
			count++
		}
	}
	log.Debug("prepared certificate", "count", count)
	return count >= 2*dsm.f+1
}

// Add one to the counter of prepare messages
func (dsm *DporStateMachine) prepareMsgPlus(h *types.Header) error {

	dsm.refreshWhenNewerHeight(h.Number.Uint64())

	// retrieve signers for checking
	signers, sigs, err := dsm.service.EcrecoverSigs(h, consensus.Preprepared)
	if err != nil {
		log.Warn("failed to recover signatures of preparing phase", "error", err)
		return err
	}
	log.Info("EcrecoverSigs: signers", "len(signers)", len(signers))

	// check the signers are validators
	validators, _ := dsm.service.ValidatorsOf(h.Number.Uint64())
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

	dsm.lock.Lock()

	log.Debug("------------- prepareMsgPlus: display merging signatures to state (before state) BEGIN ---------------",
		"len(sm.prepareSigState)", len(dsm.prepareSigState))
	idx := 0
	for k, v := range dsm.prepareSigState {
		log.Debug(fmt.Sprintf("item #%d", idx), "signer", k.Hex(), "blockHash", v.hash.Hex(), "sig", common.Bytes2Hex(v.sig[:]))
		idx++
	}
	log.Debug("------------- prepareMsgPlus: END ---------------")

	// merge signature to state
	hash := h.Hash()
	for i, s := range signers {
		dsm.prepareSigState[s] = &BlockSigItem{
			hash: hash,
			sig:  sigs[i],
		}
	}

	log.Debug("------------- prepareMsgPlus: display merging signatures to state (after state) BEGIN ---------------",
		"len(sm.prepareSigState)", len(dsm.prepareSigState))
	idx = 0
	for k, v := range dsm.prepareSigState {
		log.Debug(fmt.Sprintf("item #%d", idx), "signer", k.Hex(), "blockHash", v.hash.Hex(), "sig", common.Bytes2Hex(v.sig[:]))
		idx++
	}
	log.Debug("------------- prepareMsgPlus: END ---------------")

	dsm.lock.Unlock()

	return nil
}

// It is used to compose prepare message given a newly proposed block
func (dsm *DporStateMachine) composePrepareMsg(b *types.Block) (*types.Header, error) {
	// TODO: lock!
	if dsm.lastHeight > b.NumberU64() {
		return nil, ErrBlockTooOld
	}

	if dsm.lastHeight < b.NumberU64() {
		dsm.refreshWhenNewerHeight(b.NumberU64())
		dsm.bcache.Add(b.Hash(), b) // add to cache
	}

	// validator signs the block
	for v, item := range dsm.prepareSigState {
		dsm.service.UpdatePrepareSigsCache(v, item.hash, item.sig)
	}
	dsm.service.SignHeader(b.RefHeader(), consensus.Preprepared)
	log.Info("sign block by validator at prepare msg", "blocknum", dsm.lastHeight, "sigs", b.RefHeader().Dpor.SigsFormatText())

	dsm.prepareMsgPlus(b.Header())

	return b.Header(), nil
}

// This function is used for add the block into the cache, if a validator (prepared state) receives a proposed block that not in the cache
func (dsm *DporStateMachine) addBlockCache(b *types.Block) error {
	// dsm.lock.Lock()
	// defer dsm.lock.Unlock()
	// TODO: add lock here

	hash := b.Hash()
	_, got := dsm.bcache.Get(hash)
	if !got {
		dsm.refreshWhenNewerHeight(b.NumberU64())
		dsm.bcache.Add(b.Hash(), b) // add the impeach block into the cache
	}

	return nil
}

//It is used to propose an impeach block
func (dsm *DporStateMachine) proposeImpeachBlock() *types.Block {
	b, e := dsm.service.CreateImpeachBlock()
	if e != nil {
		log.Warn("creating impeachment block failed", "error", e)
		return nil
	}

	dsm.refreshWhenNewerHeight(b.NumberU64())
	dsm.bcache.Add(b.Hash(), b) // add the impeach block into the cache

	dsm.service.SignHeader(b.RefHeader(), consensus.ImpeachPreprepared)

	// TODO: dsm.service.SignHeader does not work;
	log.Info("proposed an impeachment block", "hash", b.Hash().Hex(), "sigs", b.Header().Dpor.SigsFormatText())

	dsm.impeachPrepareMsgPlus(b.Header())
	fmt.Printf("b.header() : %+v\n", b.Header())

	return b
}

func (dsm *DporStateMachine) composeImpeachCommitMsg(h *types.Header) (*types.Header, error) {
	return dsm.composeCommitMsg(h)
}

func (dsm *DporStateMachine) impeachCommittedCertificate(h *types.Header) bool {
	return dsm.committedCertificate(h)
}

func (dsm *DporStateMachine) composeImpeachValidateMsg(h *types.Header) (*types.Block, error) {
	return dsm.composeValidateMsg(h)
}

func (dsm *DporStateMachine) impeachCommitMsgPlus(h *types.Header) error {
	return dsm.commitMsgPlus(h)
}

func (dsm *DporStateMachine) impeachPreparedCertificate(h *types.Header) bool {
	return dsm.preparedCertificate(h)
}

func (dsm *DporStateMachine) impeachPrepareMsgPlus(h *types.Header) error {
	return dsm.prepareMsgPlus(h)
}

// It is action when a validator receive a legal pre-prepare message in Idle state
func (dsm *DporStateMachine) composePrepareMsgAction(input interface{}, defaultState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	inputBlock := input.(*types.Block)
	inputHeader := inputBlock.Header()
	ret, err := dsm.composePrepareMsg(inputBlock)
	if err != nil {
		log.Warn("error when handling pre-prepareMsg on", defaultState, "state", "error", err)
		return nil, NoAction, NoType, NoMsgCode, defaultState, err
	}

	//  Test if it has sufficed a prepared certificate
	if dsm.preparedCertificate(inputHeader) {
		ret2, err := dsm.composeCommitMsg(inputHeader)
		if err != nil {
			log.Warn("error when compose commit msg when sufficing a certificate")
			var output []interface{}
			output = append(output, ret)
			return output, BroadcastMsgAction, HeaderType, PrepareMsgCode, consensus.Preprepared, err
		}

		// For a rare case that this newly composed commit message suffice a committed certificate in a cascade
		// It is about to send out both prepare and commit message if two certificates are collected
		if dsm.committedCertificate(inputHeader) {
			log.Debug("Collect a prepare certificate and a committed certificate in Idle state, stay in Idle state")
			b, err := dsm.composeValidateMsg(inputHeader)
			if err != nil {
				log.Warn("error when handling committed certificate while collecting prepared certificate, "+
					"convert to Prepared state", "error", err)
				var output []interface{}
				output = append(output, ret)
				output = append(output, ret2)
				return output, BroadcastMultipleMsgAction, HeaderType, PrepareAndCommitMsgCode, consensus.Prepared, nil
			}
			log.Debug("Collect a committed certificate in Idle state, stay in Idle state")
			var output []interface{}
			output = append(output, b)
			return output, BroadcastAndInsertBlockAction, BlockType, ValidateMsgCode, consensus.Idle, err
		}

		log.Debug("Collect a prepared certificate in Idle state, convert to Prepared state")
		var output []interface{}
		output = append(output, ret)
		output = append(output, ret2)
		return output, BroadcastMultipleMsgAction, HeaderType, PrepareAndCommitMsgCode, consensus.Prepared, nil
	}

	log.Debug("Receive a pre-prepare message in Idle state, transit to pre-prepared state")
	var output []interface{}
	output = append(output, ret)
	return output, BroadcastMsgAction, HeaderType, PrepareMsgCode, consensus.Preprepared, nil
}

func (dsm *DporStateMachine) proposeImpeachBlockAction(input interface{}, defaultState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	// Test if its impeach prepared and committed certificate has been sufficed
	b := input.(*types.Block)
	inputHeader := b.Header()

	if dsm.impeachPreparedCertificate(inputHeader) {
		ret2, err := dsm.composeImpeachCommitMsg(inputHeader)
		if dsm.impeachCommittedCertificate(inputHeader) {
			b2, err := dsm.composeImpeachValidateMsg(inputHeader)
			if err != nil {
				log.Debug("Receive a faulty pre-prepare message, transit to impeach pre-prepared state")
				log.Warn("error when handling impeachPrepareMsg", "error", err)
				var output []interface{}
				output = append(output, b.Header())
				output = append(output, ret2)
				return output, BroadcastMultipleMsgAction, HeaderType, ImpeachPrepareAndCommitMsgCode, consensus.ImpeachPrepared, nil

			}
			log.Debug("Collect an impeach committed certificate")
			var output []interface{}
			output = append(output, b2)
			return output, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
		}
		if err != nil {
			var output []interface{}
			output = append(output, b.Header())
			log.Warn("error when composing an impeach commit message")
			return output, BroadcastMsgAction, HeaderType, ImpeachPrepareMsgCode, consensus.ImpeachPreprepared, err
		}
		log.Debug("Collect an impeach prepared certificate, transit to impeach prepared state")
		var output []interface{}
		output = append(output, b.Header())
		output = append(output, ret2)
		return output, BroadcastMultipleMsgAction, HeaderType, ImpeachPrepareAndCommitMsgCode, consensus.ImpeachPrepared, nil
	}

	log.Debug("Receive a pre-prepare message, transit to impeach pre-prepared state")
	var output []interface{}
	output = append(output, b.Header())
	return output, BroadcastMsgAction, HeaderType, ImpeachPrepareMsgCode, defaultState, nil
}

func (dsm *DporStateMachine) composeCommitMsgAction(input interface{}, defaultState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	inputHeader := input.(*types.Header)

	ret, err := dsm.composeCommitMsg(inputHeader)
	if err != nil {
		return nil, NoAction, NoType, NoMsgCode, defaultState, err
	}
	// For a rare case that newly composed commit message suffice a committed certificate
	if dsm.committedCertificate(inputHeader) {
		log.Debug("Collect a prepare certificate and a committed certificate in", defaultState, "state, convert to Idle state")
		b, err := dsm.composeValidateMsg(inputHeader)
		if err != nil {
			log.Warn("error when handling committed certificate while collecting prepared certificate, "+
				"convert to Prepared state", "error", err)
			var output []interface{}
			output = append(output, ret)
			return output, BroadcastMsgAction, HeaderType, CommitMsgCode, consensus.Prepared, nil
		}
		log.Debug("Collect a committed certificate in", defaultState, "state, stay in Idle state")
		var output []interface{}
		output = append(output, b)
		return output, BroadcastAndInsertBlockAction, BlockType, ValidateMsgCode, consensus.Idle, err

	}
	log.Debug("Collect a prepared certificate in", defaultState, "state, convert to Prepared state")
	var output []interface{}
	output = append(output, ret)
	return output, BroadcastMsgAction, HeaderType, CommitMsgCode, consensus.Prepared, nil
}

func (dsm *DporStateMachine) composeImpeachCommitMsgAction(input interface{}, defaultState consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	inputHeader := input.(*types.Header)

	ret, err := dsm.composeImpeachCommitMsg(inputHeader)

	// check if it further suffices an impeach committed certificate in a cascade
	if dsm.impeachCommittedCertificate(inputHeader) {
		b, err := dsm.composeImpeachValidateMsg(inputHeader)
		if err != nil {
			log.Warn("error when handling impeachCommitMsg on", defaultState, "state", "error", err)
			var output []interface{}
			output = append(output, ret)
			return output, BroadcastMsgAction, HeaderType, ImpeachCommitMsgCode, consensus.ImpeachPrepared, err
		}
		log.Debug("Collect an impeach committed certificate in", defaultState, "state, stay in Idle state")
		var output []interface{}
		output = append(output, b)
		return output, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
	}
	if err != nil {
		log.Warn("error when composing an impeach commit message")
		return nil, NoAction, NoType, NoMsgCode, defaultState, err
	}
	log.Debug("Collect an impeach prepared certificate in", defaultState, "state, transit to impeach prepared state")
	var output []interface{}
	output = append(output, ret)
	return output, BroadcastMsgAction, HeaderType, ImpeachCommitMsgCode, consensus.ImpeachPrepared, nil
}

// Fsm is the finite state machine for a validator, to output the correct state given on current state and inputs
// input is either a header or a block, referring to message or proposed (impeach) block
// inputType indicates the type of input
// msg indicates what type of message or block input is
// state is the current state of the validator
// the output interface is the message or block validator should handle
// the output action refers to what the validator should do with the output interface
// the output dataType indicates whether the output interface is block or header
// the output msgCode represents the type the output block or message
// the output consensus.State indicates the validator's next state
func (dsm *DporStateMachine) RealFsm(input interface{}, inputType DataType, msg MsgCode) ([]interface{}, Action, DataType, MsgCode, error) {
	state := dsm.State()

	log.Debug("state machine input", "data type", inputType, "msg code", msg, "state", state)

	output, act, dtype, msg, state, err := dsm.fsm(input, inputType, msg, state)

	log.Debug("state machine result", "action", act, "data type", dtype, "msg code", msg, "state", state, "err", err)

	dsm.SetState(state)

	return output, act, dtype, msg, nil

}

func (dsm *DporStateMachine) Fsm(input interface{}, inputType DataType, msg MsgCode) (interface{}, Action, DataType, MsgCode, error) {

	output, act, dtype, msg, _ := dsm.RealFsm(input, inputType, msg)

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
func (dsm *DporStateMachine) fsm(input interface{}, inputType DataType, msg MsgCode, state consensus.State) ([]interface{}, Action, DataType, MsgCode, consensus.State, error) {
	var inputHeader *types.Header
	var inputBlock *types.Block
	var err error

	// Determine the input is a header or a block by inputType
	switch inputType {
	case HeaderType:
		inputHeader = input.(*types.Header)
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
		return nil, NoAction, NoType, NoMsgCode, state, err
	}

	switch state {
	// The case of consensus.Idle state
	case consensus.Idle:
		switch msg {
		// Stay in consensus.Idle state if receives validate message, and we should insert the block
		case ValidateMsgCode:
			// TODO: we should add a function that verifies the legality of the validate message
			log.Debug("Receive a validate message in Idle state, stay in Idle state")
			var output []interface{}
			output = append(output, input)
			return output, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case CommitMsgCode:
			// Add one to the counter of commit messages
			err := dsm.commitMsgPlus(inputHeader)
			if dsm.committedCertificate(inputHeader) {
				b, err := dsm.composeValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling commitMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				log.Debug("Collect a committed certificate in Idle state, stay in Idle state")
				var output []interface{}
				output = append(output, b)
				return output, BroadcastAndInsertBlockAction, BlockType, ValidateMsgCode, consensus.Idle, nil
			} else {
				if err != nil {
					log.Warn("error when handling commitMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				log.Debug("Receive a commit message in Idle state, stay in Idle state")
				return nil, NoAction, NoType, NoMsgCode, consensus.Idle, nil
			}

		// Jump to consensus.Prepared state if receive 2f+1 prepare message
		case PrepareMsgCode:
			// Add one to the counter of prepare messages
			err := dsm.prepareMsgPlus(inputHeader)
			if dsm.preparedCertificate(inputHeader) {
				return dsm.composeCommitMsgAction(inputHeader, consensus.Prepared)
			} else {
				// Add one to the counter of prepare messages
				if err != nil {
					log.Warn("error when handling prepareMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				log.Debug("receive a prepare message in Idle state, stay in Idle state")
				return nil, NoAction, NoType, NoMsgCode, consensus.Idle, nil
			}

		// For the case that receive the newly proposes block or pre-prepare message
		case PreprepareMsgCode:
			// Verify the newly proposed block is faulty or not
			if dsm.verifyBlock(inputBlock) {
				// composePrepareMsgAction is going to compose a prepare msg
				// the default state Idle is due to the case composition fails
				// It further checks both certificates, forwards to corresponding state if a certificate is collected.
				return dsm.composePrepareMsgAction(inputBlock, consensus.Idle)
			} else {
				// If it is faulty, activate impeachment process
				err = ErrFsmFaultyBlock
				b := dsm.proposeImpeachBlock()
				if b != nil {
					// the default option is that it enters impeach pre-prepared phase
					// checks both impeach certificates, forwards to the corresponding state if it meets the condition
					return dsm.proposeImpeachBlockAction(b, consensus.ImpeachPreprepared)
				} else {
					log.Warn("Receive a faulty pre-prepare message in Idle state, failed to propose an impeach block")
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, ErrProposeImpeachBlockFails
				}
			}

		// Stay in consensus.Idle state and insert an impeachment block when receiving an impeach validate message
		case ImpeachValidateMsgCode:
			log.Debug("Receive an impeach validate message in Idle state, stay in Idle state")
			var output []interface{}
			output = append(output, inputBlock)
			return output, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Stay in consensus.Idle state if the validator collects 2f+1 impeach commit messages
		case ImpeachCommitMsgCode:
			// add one to impeach commit message counter
			err := dsm.impeachCommitMsgPlus(inputHeader)
			if dsm.impeachCommittedCertificate(inputHeader) {
				b, err := dsm.composeImpeachValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				log.Debug("Collect an impeach committed certificate in Idle state, stay in Idle state")
				var output []interface{}
				output = append(output, b)
				return output, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
			} else {
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				log.Debug("Receive an impeach commit message in Idle state, stay in Idle state")
				return nil, NoAction, NoType, NoMsgCode, consensus.Idle, nil
			}

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case ImpeachPrepareMsgCode:
			err := dsm.impeachPrepareMsgPlus(inputHeader)
			if dsm.impeachPreparedCertificate(inputHeader) {
				return dsm.composeImpeachCommitMsgAction(inputHeader, state)
			} else {
				if err != nil {
					log.Warn("error when handling impeachPrepareMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				log.Debug("Receive an impeach prepare message in Idle state, stay in Idle state")
				return nil, NoAction, NoType, NoMsgCode, consensus.Idle, nil
			}

		// Transit to impeach pre-prepared state if the timers expires (receiving an impeach pre-prepared message),
		// then generate the impeachment block and broadcast the impeach prepare massage
		case ImpeachPreprepareMsgCode:
			b := dsm.proposeImpeachBlock()
			if b != nil {
				// the default option is that it enters impeach pre-prepared phase
				// checks both impeach certificates, forwards to the corresponding state if it meets the condition
				return dsm.proposeImpeachBlockAction(b, consensus.ImpeachPreprepared)
			} else {
				log.Warn("Error when receiving an impeach pre-prepare message in Idle state, failed to propose an impeach block")
				return nil, NoAction, NoType, NoMsgCode, consensus.Idle, ErrProposeImpeachBlockFails
			}

		default:
			log.Warn("unexpected input for Idle state")
			err = ErrFsmWrongIdleInput
		}

	// The case of pre-prepared state
	case consensus.Preprepared:
		switch msg {
		// Jump to committed state if receive a validate message
		case ValidateMsgCode:
			log.Debug("Receive a validate message in Pre-prepared state, transit to Idle state")
			var output []interface{}
			output = append(output, inputBlock)
			return output, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Jump to committed state if receive 2f+1 commit messages
		case CommitMsgCode:
			// Add one to the counter of commit messages
			err := dsm.commitMsgPlus(inputHeader)
			if dsm.committedCertificate(inputHeader) {
				b, err := dsm.composeValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling commitMsg on Pre-prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				log.Debug("Collect a committed certificate in Pre-prepared state, transit to Idle state")
				var output []interface{}
				output = append(output, b)
				return output, BroadcastAndInsertBlockAction, BlockType, ValidateMsgCode, consensus.Idle, nil
			} else {
				if err != nil {
					log.Warn("error when handling commitMsg on Pre-prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				log.Debug("Receive a commit message in Pre-prepared state, stay in Pre-prepare state")
				return nil, NoAction, NoType, NoMsgCode, consensus.Preprepared, nil
			}
		// Convert to consensus.Prepared state if collect prepared certificate
		case PrepareMsgCode:
			// Add one to the counter of prepare messages
			err := dsm.prepareMsgPlus(inputHeader)
			if dsm.preparedCertificate(inputHeader) {
				log.Debug("Collect a prepared certificate in Pre-prepared state, transit to Prepared state")
				return dsm.composeCommitMsgAction(inputHeader, state)
			} else {
				if err != nil {
					log.Warn("error when handling prepareMsg on Pre-prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Preprepared, err
				}
				log.Debug("Receive a prepare message in Pre-prepared state, stay in Pre-prepare state")
				return nil, NoAction, NoType, NoMsgCode, consensus.Preprepared, nil
			}
		case ImpeachValidateMsgCode:
			log.Debug("Receive an impeach validate message in Pre-prepared state, transit to Idle state")
			var output []interface{}
			output = append(output, inputBlock)
			return output, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case ImpeachCommitMsgCode:
			// Add one to the counter of commit messages
			err := dsm.impeachCommitMsgPlus(inputHeader)
			if dsm.impeachCommittedCertificate(inputHeader) {
				b, err := dsm.composeImpeachValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Preprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Preprepared, err
				}
				log.Debug("Collect an impeach committed certificate in Pre-prepared state, transit to Idle state")
				var output []interface{}
				output = append(output, b)
				return output, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
			} else {
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Preprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Preprepared, err
				}
				log.Debug("Receive an impeach commit message in Pre-prepared state, stay in Pre-prepare state")
				return nil, NoAction, NoType, NoMsgCode, consensus.Idle, nil
			}

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case ImpeachPrepareMsgCode:
			err := dsm.impeachPrepareMsgPlus(inputHeader)
			if dsm.impeachPreparedCertificate(inputHeader) {
				return dsm.composeImpeachCommitMsgAction(inputHeader, state)
				//ret, err := dsm.composeImpeachCommitMsg(inputHeader)
				//if err != nil {
				//	log.Warn("error when composing an impeach commit message")
				//	return nil, NoAction, NoType, NoMsgCode, state, err
				//}
				//log.Debug("Collect an impeach prepared certificate in Pre-prepared state, transit to impeach prepared state")
				//return ret, BroadcastMsgAction, HeaderType, ImpeachCommitMsgCode, consensus.ImpeachPrepared, nil
			} else {
				if err != nil {
					log.Warn("error when handling impeachPrepareMsg on Preprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Preprepared, err
				}
				log.Debug("Receive an impeach prepare message in Pre-prepared state, stay in Pre-prepare state")
				return nil, NoAction, NoType, NoMsgCode, consensus.Preprepared, nil
			}

		// when the timer expires, the validator is about to propose an impeachment block
		case ImpeachPreprepareMsgCode:
			b := dsm.proposeImpeachBlock()
			if b != nil {
				log.Debug("Receive an impeach pre-prepare message in Pre-prepared state, transit to impeach pre-prepared state")
				// the default option is that it enters impeach pre-prepared phase
				// checks both impeach certificates, forwards to the corresponding state if it meets the condition
				return dsm.proposeImpeachBlockAction(b, consensus.ImpeachPreprepared)
				// return b.Header(), BroadcastMsgAction, HeaderType, ImpeachPrepareMsgCode, consensus.ImpeachPreprepared, nil
			} else {
				log.Warn("error when proposing impeach block")
				return nil, NoAction, NoType, NoMsgCode, consensus.Idle, ErrProposeImpeachBlockFails
			}

		default:
			log.Warn("unexpected input for pre-prepared state")
			err = ErrFsmWrongPrepreparedInput
		}

	// The case of consensus.Prepared stage
	case consensus.Prepared:
		switch msg {
		// Jump to committed state if receive a validate message
		case ValidateMsgCode:
			log.Debug("Receive a validate message in Prepared state, transit to Idle state")
			var output []interface{}
			output = append(output, inputBlock)
			return output, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// convert to committed state if collects committed certificate
		case CommitMsgCode:
			// Add one to the counter of commit messages
			err := dsm.commitMsgPlus(inputHeader)
			if dsm.committedCertificate(inputHeader) {
				b, err := dsm.composeValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling commitMsg on Prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, err
				}
				log.Debug("Collect a committed certificate in Prepared state, transit to Idle state")
				var output []interface{}
				output = append(output, b)
				return output, BroadcastAndInsertBlockAction, BlockType, ValidateMsgCode, consensus.Idle, nil
			} else {
				if err != nil {
					log.Warn("error when handling commitMsg on Prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, err
				}
				log.Debug("Receive a commit message in Prepared state, stay in prepared state")
				return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, nil
			}

		// Transit to consensus.Idle state to insert impeach block
		case ImpeachValidateMsgCode:
			log.Debug("Receive an impeach validate message in Prepared state, transit to Idle state")
			var output []interface{}
			output = append(output, inputBlock)
			return output, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Transit to consensus.Idle state to committed state if receive 2f+1 commit messages
		case ImpeachCommitMsgCode:
			// Add one to the counter of impeach commit messages
			err := dsm.impeachCommitMsgPlus(inputHeader)
			if dsm.impeachCommittedCertificate(inputHeader) {
				b, err := dsm.composeImpeachValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, err
				}
				log.Debug("Collect an impeach committed certificate in Prepared state, transit to Idle state")
				var output []interface{}
				output = append(output, b)
				return output, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
			} else {
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, err
				}
				log.Debug("Receive an impeach committed certificate in Prepared state, stay in Prepared state")
				return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, nil
			}

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case ImpeachPrepareMsgCode:
			err := dsm.impeachPrepareMsgPlus(inputHeader)
			if dsm.impeachPreparedCertificate(inputHeader) {
				return dsm.composeImpeachCommitMsgAction(inputHeader, state)
				//ret, err := dsm.composeImpeachCommitMsg(inputHeader)
				//if err != nil {
				//	log.Warn("error when composing an impeach commit message")
				//	return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, err
				//}
				//log.Debug("Collect an impeach prepared certificate in Prepared state, transit to impeach prepared state")
				//return ret, BroadcastMsgAction, HeaderType, ImpeachCommitMsgCode, consensus.ImpeachPrepared, nil
			} else {
				if err != nil {
					log.Warn("error when handling impeachPrepareMsg on Prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, err
				}
				log.Debug("Receive an impeach prepare message in Prepared state, stay in Prepared state")
				return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, nil
			}

		// when the timer expires, the validator is about to propose an impeachment block
		case ImpeachPreprepareMsgCode:
			b := dsm.proposeImpeachBlock()
			if b != nil {
				log.Debug("Receive an impeach pre-prepare message in Prepared state, transit to impeach Pre-prepared state")
				return dsm.proposeImpeachBlockAction(b, consensus.ImpeachPreprepared)
				// return b.Header(), BroadcastMsgAction, HeaderType, ImpeachPrepareMsgCode, consensus.ImpeachPreprepared, nil
			} else {
				log.Warn("error when proposing an impeach block")
				return nil, NoAction, NoType, NoMsgCode, consensus.Idle, ErrProposeImpeachBlockFails
			}

		// If the validator in prepared state has not received the block, check its verification and add its to the cache
		case PreprepareMsgCode:
			if dsm.preparedCertificate(inputBlock.Header()) {
				dsm.addBlockCache(inputBlock)
			}

		default:
			log.Warn("unexpected input for prepared state")
			err = ErrFsmWrongPreparedInput

		}

	case consensus.ImpeachPreprepared:
		switch msg {
		// Transit to consensus.Idle state when receiving impeach validate message
		case ImpeachValidateMsgCode:
			log.Debug("Receive an impeach validate message in impeach pre-prepared state, transit to Idle state")
			var output []interface{}
			output = append(output, inputBlock)
			return output, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case ImpeachCommitMsgCode:
			// Add one to the counter of commit messages
			err := dsm.impeachCommitMsgPlus(inputHeader)
			if dsm.impeachCommittedCertificate(inputHeader) {
				b, err := dsm.composeImpeachValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Impeach Pre-prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPreprepared, err
				}
				log.Debug("Collect an impeach committed certificate in impeach pre-prepared state, transit to Idle state")
				var output []interface{}
				output = append(output, b)
				return output, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
			} else {
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Impeach Pre-prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPreprepared, err
				}
				log.Debug("Receive an impeach commit message in impeach pre-prepared state, stay in Impeach pre-prepared state")
				return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPreprepared, nil
			}

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case ImpeachPrepareMsgCode:
			err := dsm.impeachPrepareMsgPlus(inputHeader)
			if dsm.impeachPreparedCertificate(inputHeader) {
				return dsm.composeImpeachCommitMsgAction(inputHeader, state)
				//ret, err := dsm.composeImpeachCommitMsg(inputHeader)
				//if err != nil {
				//	log.Warn("error when composing an impeach commit message")
				//	return nil, NoAction, NoType, NoMsgCode, state, err
				//}
				//log.Debug("Collect an impeach prepared certificate in impeach pre-prepared state, transit to Impeach prepared state")
				//return ret, BroadcastMsgAction, HeaderType, ImpeachCommitMsgCode, consensus.ImpeachPrepared, nil
			} else {
				if err != nil {
					log.Warn("error when handling impeachPrepareMsg on ImpeachPreprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPreprepared, err
				}
				log.Debug("Receive an impeach prepare message in impeach pre-prepared state, stay in Impeach pre-prepared state")
				return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPreprepared, nil
			}

		// Do nothing if receives multiple impeach prepared
		case ImpeachPreprepareMsgCode:
			log.Debug("Receives an impeach pre-prepare message in impeach pre-prepared state, do nothing")
			return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPrepared, nil
		default:
			log.Debug("unexpected input for impeach pre-prepared state, do nothing")
			err = ErrFsmWrongImpeachPrepreparedInput
		}

	case consensus.ImpeachPrepared:
		switch msg {
		// Transit to consensus.Idle state when receiving impeach validate message
		case ImpeachValidateMsgCode:
			log.Debug("Receive an impeach validate message in impeach prepared state, transit to Idle state")
			var output []interface{}
			output = append(output, inputBlock)
			return output, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case ImpeachCommitMsgCode:
			// Add one to the counter of commit messages
			err := dsm.impeachCommitMsgPlus(inputHeader)
			if dsm.impeachCommittedCertificate(inputHeader) {
				b, err := dsm.composeImpeachValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on ImpeachPrepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPrepared, err
				}
				log.Debug("Collect an impeach committed certificate in impeach prepared state, transit to Idle state")
				var output []interface{}
				output = append(output, b)
				return output, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
			} else {
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on ImpeachPrepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPrepared, err
				}
				log.Debug("Receive an impeach commit message in impeach prepared state, stay in Impeach prepared state")
				return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPrepared, nil
			}
		case ImpeachPreprepareMsgCode:
			// resend impeachment block
			b := dsm.proposeImpeachBlock()
			if b != nil {
				log.Debug("propose again an impeach pre-prepare message")
				return dsm.proposeImpeachBlockAction(b, consensus.ImpeachPreprepared)
				// return b.Header(), BroadcastMsgAction, HeaderType, ImpeachPrepareMsgCode, consensus.ImpeachPreprepared, nil
			} else {
				log.Warn("error when proposing an impeachment block")
				return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPrepared, ErrProposeImpeachBlockFails
			}
		default:
			log.Warn("unexpected input for impeach prepared state")
			err = ErrFsmWrongImpeachPreparedInput
		}

		// Broadcast a validate message and then go back to consensus.Idle state
		//case committed:
		///return sm.composeValidateMsg(inputHeader), broadcastAndInsertBlock, block, validateMsg, consensus.Idle, nil
		// Broadcast a validate message and then go back to consensus.Idle state
		//case committed:
		//	return composeValidateMsg(inputHeader), broadcastAndInsertBlock, block, validateMsg, consensus.Idle, nil

		// Insert the block and go back to consensus.Idle state
		//case inserting:
		//	return inputBlock, insertBlock, block, noMsg, consensus.Idle, nil
	}

	// Do nothing if the validator receive an unexpected unexpected info
	return nil, NoAction, NoType, NoMsgCode, state, err
}
