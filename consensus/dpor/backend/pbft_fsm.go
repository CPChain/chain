package backend

import (
	"bytes"
	"errors"
	"sync"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	lru "github.com/hashicorp/golang-lru"
)

//Type enumerator for FSM action
type Action uint8

const (
	NoAction Action = iota
	BroadcastMsgAction
	InsertBlockAction
	BroadcastAndInsertBlockAction
)

//Type enumerator for FSM output
type DataType uint8

const (
	NoType DataType = iota
	HeaderType
	BlockType
	ImpeachBlockType
)

//Type enumerator for FSM message type
type MsgCode uint8

const (
	NoMsgCode MsgCode = iota
	PreprepareMsgCode
	PrepareMsgCode
	CommitMsgCode
	ValidateMsgCode
	ImpeachPreprepareMsgCode
	ImpeachPrepareMsgCode
	ImpeachCommitMsgCode
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

// commitCertificate is true if the validator has collected 2f+1 commit messages
func (dsm *DporStateMachine) commitCertificate(h *types.Header) bool {
	dsm.lock.RLock()
	defer dsm.lock.RUnlock()

	hash := h.Hash()
	var count uint64 = 0
	for _, item := range dsm.commitSigState {
		if bytes.Equal(item.hash[:], hash[:]) {
			// TODO: @AC it had better to check whether the signature is valid for safety, consider add the check in future
			count++
		}
	}

	log.Debug("commit certificate", "count", count)
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
			if state.hash == hash { // if the validator signed the block, use its signature
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
			log.Warn("a signer is not in validator committee", "signer", s.Hex())
			checkErr = consensus.ErrInvalidSigners
		}
	}
	if checkErr != nil {
		return checkErr
	}

	dsm.lock.Lock()

	// merge signature to state
	hash := h.Hash()
	for i, s := range signers {
		dsm.commitSigState[s] = &BlockSigItem{
			hash: hash,
			sig:  sigs[i],
		}
	}

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

	return h, nil
}

//prepareCertificate is true if the validator has collects 2f+1 prepare messages
func (dsm *DporStateMachine) prepareCertificate(h *types.Header) bool {
	dsm.lock.RLock()
	defer dsm.lock.RUnlock()

	hash := h.Hash()
	var count uint64 = 0
	for _, item := range dsm.prepareSigState {
		if bytes.Equal(item.hash[:], hash[:]) {
			// TODO: @AC it had better to check whether the signature is valid for safety, consider add the check in future
			count++
		}
	}
	log.Debug("prepare certificate", "count", count)
	return count >= 2*dsm.f+1
}

// Add one to the counter of prepare messages
func (dsm *DporStateMachine) prepareMsgPlus(h *types.Header) error {

	dsm.refreshWhenNewerHeight(h.Number.Uint64())

	// retrieve signers for checking
	signers, sigs, err := dsm.service.EcrecoverSigs(h, consensus.Prepared)
	if err != nil {
		log.Warn("failed to recover signatures of preparing phase", "error", err)
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
			log.Warn("a signer is not in validator committee", "signer", s.Hex())
			checkErr = consensus.ErrInvalidSigners
		}
	}
	if checkErr != nil {
		return checkErr
	}

	dsm.lock.Lock()

	// merge signature to state
	hash := h.Hash()
	for i, s := range signers {
		dsm.prepareSigState[s] = &BlockSigItem{
			hash: hash,
			sig:  sigs[i],
		}
	}
	dsm.lock.Unlock()

	return nil
}

// It is used to compose prepare message given a newly proposed block
func (dsm *DporStateMachine) composePrepareMsg(b *types.Block) (*types.Header, error) {
	// TODO: lock!
	if dsm.lastHeight >= b.NumberU64() {
		return nil, ErrBlockTooOld
	}

	dsm.refreshWhenNewerHeight(b.NumberU64())
	dsm.bcache.Add(b.Hash(), b) // add to cache
	// validator signs the block
	for v, item := range dsm.prepareSigState {
		dsm.service.UpdatePrepareSigsCache(v, item.hash, item.sig)
	}
	dsm.service.SignHeader(b.RefHeader(), consensus.Preprepared)
	log.Info("sign block by validator at prepare msg", "blocknum", dsm.lastHeight, "sigs", b.RefHeader().Dpor.SigsFormatText())

	return b.Header(), nil
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

	dsm.service.SignHeader(b.RefHeader(), consensus.Preprepared)
	log.Info("proposed an impeachment block", "hash", b.Hash().Hex(), "sigs", b.Header().Dpor.SigsFormatText())
	return b
}

func (dsm *DporStateMachine) impeachCommitCertificate(h *types.Header) bool {
	return dsm.commitCertificate(h)
}

func (dsm *DporStateMachine) composeImpeachValidateMsg(h *types.Header) (*types.Block, error) {
	return dsm.composeValidateMsg(h)
}

func (dsm *DporStateMachine) impeachCommitMsgPlus(h *types.Header) error {
	return dsm.commitMsgPlus(h)
}

func (dsm *DporStateMachine) impeachPrepareCertificate(h *types.Header) bool {
	return dsm.prepareCertificate(h)
}

func (dsm *DporStateMachine) impeachPrepareMsgPlus(h *types.Header) error {
	return dsm.prepareMsgPlus(h)
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
func (dsm *DporStateMachine) Fsm(input interface{}, inputType DataType, msg MsgCode) (interface{}, Action, DataType, MsgCode, error) {
	state := dsm.State()

	log.Debug("state machine input", "data type", inputType, "msg code", msg, "state", state)

	output, act, dtype, msg, state, err := dsm.fsm(input, inputType, msg, state)

	log.Debug("state machine result", "action", act, "data type", dtype, "msg code", msg, "state", state, "err", err)

	dsm.SetState(state)

	return output, act, dtype, msg, err
}

func (dsm *DporStateMachine) fsm(input interface{}, inputType DataType, msg MsgCode, state consensus.State) (interface{}, Action, DataType, MsgCode, consensus.State, error) {
	var inputHeader *types.Header
	var inputBlock *types.Block
	var err error

	// Determine the input is a header or a block by inputType
	switch inputType {
	case HeaderType:
		inputHeader = input.(*types.Header)
	case BlockType:
		inputBlock = input.(*types.Block)
	case ImpeachBlockType:
		inputBlock = input.(*types.Block)
	// If input == nil and inputType == noType, it means the the timer of validator expires
	case NoType:
		if input != nil {
			err = ErrFsmWrongDataType
		}
	default:
		err = ErrFsmWrongDataType
		return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
	}

	switch state {
	// The case of consensus.Idle state
	case consensus.Idle:
		switch msg {
		// Stay in consensus.Idle state if receives validate message, and we should insert the block
		case ValidateMsgCode:
			return inputBlock, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case CommitMsgCode:
			if dsm.commitCertificate(inputHeader) {
				b, err := dsm.composeValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling commitMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				return b, BroadcastAndInsertBlockAction, BlockType, ValidateMsgCode, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				err := dsm.commitMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling commitMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.Idle, nil
			}

		// Jump to consensus.Prepared state if receive 2f+1 prepare message
		case PrepareMsgCode:
			if dsm.prepareCertificate(inputHeader) {
				ret, err := dsm.composeCommitMsg(inputHeader)
				if err != nil {
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				return ret, BroadcastMsgAction, HeaderType, CommitMsgCode, consensus.Prepared, nil
			} else {
				// Add one to the counter of prepare messages
				err := dsm.prepareMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling prepareMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.Idle, nil
			}

		// For the case that receive the newly proposes block or pre-prepare message
		case PreprepareMsgCode:
			// Verify the newly proposed block is faulty or not
			if dsm.verifyBlock(inputBlock) {
				ret, err := dsm.composePrepareMsg(inputBlock)
				if err != nil {
					log.Warn("error when handling preprepareMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				return ret, BroadcastMsgAction, HeaderType, PrepareMsgCode, consensus.Preprepared, nil
			} else {
				// If it is faulty, activate impeachment process
				err = ErrFsmFaultyBlock
				b := dsm.proposeImpeachBlock()
				if b != nil {
					return b.Header(), BroadcastMsgAction, HeaderType, ImpeachPrepareMsgCode, consensus.ImpeachPreprepared, err
				} else {
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, ErrProposeImpeachBlockFails
				}
			}

		// Stay in consensus.Idle state and insert an impeachment block when receiving an impeach validate message
		case ImpeachValidateMsgCode:
			return inputBlock, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Stay in consensus.Idle state if the validator collects 2f+1 impeach commit messages
		case ImpeachCommitMsgCode:
			if dsm.impeachCommitCertificate(inputHeader) {
				b, err := dsm.composeImpeachValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				return b, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
			} else {
				err := dsm.impeachCommitMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				return inputHeader, NoAction, NoType, NoMsgCode, consensus.Idle, nil
			}

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case ImpeachPrepareMsgCode:
			if dsm.impeachPrepareCertificate(inputHeader) {
				return inputHeader, BroadcastMsgAction, HeaderType, ImpeachCommitMsgCode, consensus.ImpeachPrepared, nil
			} else {
				err := dsm.impeachPrepareMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachPrepareMsg on Idle state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.Idle, nil
			}

		// Transit to impeach pre-prepared state if the timers expires (receiving a impeach pre-prepared message),
		// then generate the impeachment block and broadcast the impeach prepare massage
		case ImpeachPreprepareMsgCode:
			b := dsm.proposeImpeachBlock()
			if b != nil {
				return b.Header(), BroadcastMsgAction, HeaderType, ImpeachPrepareMsgCode, consensus.ImpeachPreprepared, nil
			} else {
				return nil, NoAction, NoType, NoMsgCode, consensus.Idle, ErrProposeImpeachBlockFails
			}

		default:
			err = ErrFsmWrongIdleInput
		}

	// The case of pre-prepared state
	case consensus.Preprepared:
		switch msg {
		// Jump to committed state if receive a validate message
		case ValidateMsgCode:
			return inputBlock, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Jump to committed state if receive 2f+1 commit messages
		case CommitMsgCode:
			if dsm.commitCertificate(inputHeader) {
				b, err := dsm.composeValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling commitMsg on Preprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				return b, BroadcastAndInsertBlockAction, BlockType, ValidateMsgCode, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				err := dsm.commitMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling commitMsg on Preprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Idle, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.Preprepared, nil
			}
		// Convert to consensus.Prepared state if collect prepare certificate
		case PrepareMsgCode:
			if dsm.prepareCertificate(inputHeader) {
				ret, err := dsm.composeCommitMsg(inputHeader)
				if err != nil {
					return nil, NoAction, NoType, NoMsgCode, consensus.Preprepared, err
				}
				return ret, BroadcastMsgAction, HeaderType, CommitMsgCode, consensus.Prepared, nil
			} else {
				// Add one to the counter of prepare messages
				err := dsm.prepareMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling prepareMsg on Preprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Preprepared, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.Preprepared, nil
			}
		case ImpeachValidateMsgCode:
			return inputBlock, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case ImpeachCommitMsgCode:
			if dsm.impeachCommitCertificate(inputHeader) {
				b, err := dsm.composeImpeachValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Preprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Preprepared, err
				}
				return b, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				err := dsm.commitMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Preprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Preprepared, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.Idle, nil
			}

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case ImpeachPrepareMsgCode:
			if dsm.impeachPrepareCertificate(inputHeader) {
				return inputHeader, BroadcastMsgAction, HeaderType, ImpeachCommitMsgCode, consensus.ImpeachPrepared, nil
			} else {
				err := dsm.impeachPrepareMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachPrepareMsg on Preprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Preprepared, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.Preprepared, nil
			}

		// when the timer expires, the validator is about to propose an impeachment block
		case ImpeachPreprepareMsgCode:
			b := dsm.proposeImpeachBlock()
			if b != nil {
				return b.Header(), BroadcastMsgAction, HeaderType, ImpeachPrepareMsgCode, consensus.ImpeachPreprepared, nil
			} else {
				return nil, NoAction, NoType, NoMsgCode, consensus.Idle, ErrProposeImpeachBlockFails
			}

		default:
			err = ErrFsmWrongPrepreparedInput
		}

	// The case of consensus.Prepared stage
	case consensus.Prepared:
		switch msg {
		// Jump to committed state if receive a validate message
		case ValidateMsgCode:
			return inputBlock, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// convert to committed state if collects commit certificate
		case CommitMsgCode:
			if dsm.commitCertificate(inputHeader) {
				b, err := dsm.composeValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling commitMsg on Prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, err
				}
				return b, BroadcastAndInsertBlockAction, BlockType, ValidateMsgCode, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				err := dsm.commitMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling commitMsg on Prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.Preprepared, nil
			}

		// Transit to consensus.Idle state to insert impeach block
		case ImpeachValidateMsgCode:
			return inputBlock, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Transit to consensus.Idle state to committed state if receive 2f+1 commit messages
		case ImpeachCommitMsgCode:
			if dsm.impeachCommitCertificate(inputHeader) {
				b, err := dsm.composeImpeachValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, err
				}
				return b, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				err := dsm.impeachCommitMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on Prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.Prepared, nil
			}

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case ImpeachPrepareMsgCode:
			if dsm.impeachPrepareCertificate(inputHeader) {
				return inputHeader, BroadcastMsgAction, HeaderType, ImpeachCommitMsgCode, consensus.ImpeachPrepared, nil
			} else {
				err := dsm.impeachPrepareMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachPrepareMsg on Prepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.Prepared, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.Prepared, nil
			}

		// when the timer expires, the validator is about to propose an impeachment block
		case ImpeachPreprepareMsgCode:
			b := dsm.proposeImpeachBlock()
			if b != nil {
				return b.Header(), BroadcastMsgAction, HeaderType, ImpeachPrepareMsgCode, consensus.ImpeachPreprepared, nil
			} else {
				return nil, NoAction, NoType, NoMsgCode, consensus.Idle, ErrProposeImpeachBlockFails
			}

		default:
			err = ErrFsmWrongPreparedInput

		}

	case consensus.ImpeachPreprepared:
		switch msg {
		// Transit to consensus.Idle state when receiving impeach validate message
		case ImpeachValidateMsgCode:
			return inputBlock, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case ImpeachCommitMsgCode:
			if dsm.impeachCommitCertificate(inputHeader) {
				b, err := dsm.composeImpeachValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on ImpeachPreprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPreprepared, err
				}
				return b, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				err := dsm.impeachCommitMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on ImpeachPreprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPreprepared, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.ImpeachPreprepared, nil
			}

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case ImpeachPrepareMsgCode:
			if dsm.impeachPrepareCertificate(inputHeader) {
				return inputHeader, BroadcastMsgAction, HeaderType, ImpeachCommitMsgCode, consensus.ImpeachPrepared, nil
			} else {
				err := dsm.impeachPrepareMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachPrepareMsg on ImpeachPreprepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPreprepared, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.ImpeachPreprepared, nil
			}
		default:
			err = ErrFsmWrongImpeachPrepreparedInput
		}

	case consensus.ImpeachPrepared:
		switch msg {
		// Transit to consensus.Idle state when receiving impeach validate message
		case ImpeachValidateMsgCode:
			return inputBlock, InsertBlockAction, BlockType, NoMsgCode, consensus.Idle, nil

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case ImpeachCommitMsgCode:
			if dsm.impeachCommitCertificate(inputHeader) {
				b, err := dsm.composeImpeachValidateMsg(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on ImpeachPrepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPrepared, err
				}
				return b, BroadcastAndInsertBlockAction, BlockType, ImpeachValidateMsgCode, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				err := dsm.impeachCommitMsgPlus(inputHeader)
				if err != nil {
					log.Warn("error when handling impeachCommitMsg on ImpeachPrepared state", "error", err)
					return nil, NoAction, NoType, NoMsgCode, consensus.ImpeachPrepared, err
				}
				return input, NoAction, NoType, NoMsgCode, consensus.ImpeachPrepared, nil
			}
		default:
			err = ErrFsmWrongPreparedInput
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

	return nil, NoAction, NoType, NoMsgCode, state, err
}
