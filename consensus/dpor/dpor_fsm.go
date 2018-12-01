package dpor

import (
	"errors"
	"sync"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"

	"bitbucket.org/cpchain/chain/types"
)

//Type enumerator for FSM action
type action uint8

const (
	noAction action = iota
	broadcastMsg
	insertBlock
	broadcastAndInsertBlock
)

//Type enumerator for FSM output
type dataType uint8

const (
	noType dataType = iota
	header
	block
	impeachBlock
)

//Type enumerator for FSM message type
type msgCode uint8

const (
	noMsg msgCode = iota
	preprepareMsg
	prepareMsg
	commitMsg
	validateMsg
	impeachPreprepareMsg
	impeachPrepareMsg
	impeachCommitMsg
	impeachValidateMsg
)

var (
	errBlockTooOld = errors.New("the block is too old")
)

//Type enumerator for FSM states

type sigRecord struct {
	prepareSigs Signatures
	commitSigs  Signatures
}

type DporSm struct {
	lock sync.RWMutex

	service   backend.DporService
	state     map[uint64]*sigRecord
	f         uint64
	lastBlock *types.Block
}

// getSigState returns the pointer to the message state of a specified block number
func (sm *DporSm) getSigState(h *types.Header) *sigRecord {
	rec, found := sm.state[h.Number.Uint64()]
	if !found {
		rec = &sigRecord{}
		sm.state[h.Number.Uint64()] = rec
	}
	return rec

	//TODO: sm.state cannot use block.number as key, @chengx
}

// resetMsgState resets a messsage state of a specified block number
func (sm *DporSm) resetMsgState(h *types.Header) {
	sm.state[h.Number.Uint64()] = &sigRecord{}
}

// verifyBlock is a func to verify whether the block is legal
func (sm *DporSm) verifyBlock(block *types.Block) bool {
	sm.lock.RLock()
	defer sm.lock.RUnlock()

	return sm.service.ValidateBlock(block) == nil
}

// commitCertificate is true if the validator has collected 2f+1 commit messages
func (sm *DporSm) commitCertificate(h *types.Header) bool {
	sm.lock.RLock()
	defer sm.lock.RUnlock()

	state := sm.getSigState(h)
	return uint64(len(state.commitSigs.sigs)) >= 2*sm.f+1
}

//composeValidateMsg is to return the validate message, which is the proposed block or impeach block
func (sm *DporSm) composeValidateMsg(h *types.Header) *types.Block {
	return sm.lastBlock
}

//Add one to the counter of commit messages
func (sm *DporSm) commitMsgPlus(h *types.Header) {
	sm.lock.Lock()
	defer sm.lock.Unlock()

	state := sm.getSigState(h)
	signers, err := sm.service.EcrecoverSigs(h, consensus.Prepared)
	if err != nil {
		log.Warn("failed to recover signatures of committing phase", "error", err)
		return
	}

	validators, _ := sm.service.ValidatorsOf(h.Number.Uint64())
	// merge signature to state
	for i, s := range signers {
		for _, v := range validators {
			if s == v {
				state.commitSigs.SetSig(s, h.Dpor.Sigs[i][:])
				break
			}
		}
	}
}

func (sm *DporSm) composeCommitMsg(h *types.Header) (*types.Header, error) {
	if sm.lastBlock.Number().Cmp(h.Number) >= 0 {
		return nil, errBlockTooOld
	}

	validators, _ := sm.service.ValidatorsOf(h.Number.Uint64())
	// clean up PREPARE signatures
	h.Dpor.Sigs = make([]types.DporSignature, len(validators))
	sm.service.SignHeader(h, consensus.Committing)
	log.Info("sign block by validator at commit phase", "blocknum", sm.lastBlock.Number(), "sigs", sm.lastBlock.RefHeader().Dpor.SigsFormatText())
	return h, nil
}

//prepareCertificate is true if the validator has collects 2f+1 prepare messages
func (sm *DporSm) prepareCertificate(h *types.Header) bool {
	sm.lock.RLock()
	defer sm.lock.RUnlock()

	return uint64(len(sm.getSigState(h).prepareSigs.sigs)) >= 2*sm.f+1
}

//Add one to the counter of prepare messages
func (sm *DporSm) prepareMsgPlus(h *types.Header) {
	sm.lock.Lock()
	defer sm.lock.Unlock()

	state := sm.getSigState(h)
	signers, err := sm.service.EcrecoverSigs(h, consensus.Preprepared)
	if err != nil {
		log.Warn("failed to recover signatures of preparing phase", "error", err)
		return
	}

	validators, _ := sm.service.ValidatorsOf(h.Number.Uint64())
	// merge signature to state
	for i, s := range signers {
		for _, v := range validators {
			if s == v {
				state.prepareSigs.SetSig(s, h.Dpor.Sigs[i][:])
				break
			}
		}
	}
}

func (sm *DporSm) composePrepareMsg(b *types.Block) (*types.Header, error) {
	if sm.lastBlock.Number().Cmp(b.Number()) >= 0 {
		return nil, errBlockTooOld
	}

	sm.lastBlock = b
	sm.resetMsgState(b.Header())
	// validator signs the block
	sm.service.SignHeader(b.RefHeader(), consensus.Preparing)
	log.Info("sign block by validator at prepare phase", "blocknum", sm.lastBlock.Number(), "sigs", sm.lastBlock.RefHeader().Dpor.SigsFormatText())

	return b.Header(), nil
}

//It is used to propose an impeach block
func (sm *DporSm) proposeImpeachBlock() *types.Block {
	b, e := sm.service.CreateImpeachBlock()
	if e != nil {
		log.Warn("creating impeachment block failed", "error", e)
		return nil
	}
	return b
}

//It returns true if the timer expires
func impeachTimer() bool {
	//TODO: @shiyc
	return false
}

//composeImpeachValidateMsg is to return the impeachment validate message, which is the proposed block or impeach block
func (sm *DporSm) composeImpeachValidateMsg(h *types.Header) *types.Block {
	return sm.lastBlock
}

// It returns true it collects 2f+1 impeach prepare messages
func (sm *DporSm) impeachPrepareCertificate(h *types.Header) bool {
	//TODO @shiyc implement it
	return true
}

func (sm *DporSm) impeachPrepareMsgPlus(h *types.Header) {
	//TODO @shiyc
}

func (sm *DporSm) composeImpeachCommitMsg(h *types.Header) *types.Header {
	return h
}

func (sm *DporSm) impeachCommitCertificate(h *types.Header) bool {
	//TODO @shiyc implement it
	return true
}

func (sm *DporSm) impeachCommitMsgPlus(h *types.Header) {
	//TODO @shiyc implement it
}

// Fsm is the finite state machine for a validator, to output the correct state given on current state and inputs
func (sm *DporSm) Fsm(input interface{}, inputType dataType, msg msgCode, state consensus.State) (interface{}, action, dataType, msgCode, consensus.State, error) {
	var inputHeader *types.Header
	var inputBlock *types.Block
	var err error

	// Determine the input is a header or a block
	switch inputType {
	case header:
		inputHeader = input.(*types.Header)
	case block:
		inputBlock = input.(*types.Block)
	case impeachBlock:
		inputBlock = input.(*types.Block)
	default:
		err = errors.New("an unexpected input data type")
		return nil, noAction, noType, noMsg, consensus.Idle, err
	}

	switch state {
	// The case of consensus.Idle state
	case consensus.Idle:
		switch msg {
		// Stay in consensus.Idle state if receives validate message, and we should insert the block
		case validateMsg:
			return inputBlock, insertBlock, block, noMsg, consensus.Idle, nil

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case commitMsg:
			if sm.commitCertificate(inputHeader) {
				return sm.composeValidateMsg(inputHeader), broadcastAndInsertBlock, block, validateMsg, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				sm.commitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.Idle, nil
			}

		// Jump to consensus.Prepared state if receive 2f+1 prepare message
		case prepareMsg:
			if sm.prepareCertificate(inputHeader) {
				ret, err := sm.composeCommitMsg(inputHeader)
				if err != nil {
					return nil, noAction, noType, noMsg, consensus.Idle, err
				}
				return ret, broadcastMsg, header, commitMsg, consensus.Prepared, nil
			} else {
				// Add one to the counter of prepare messages
				sm.prepareMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.Idle, nil
			}

		// For the case that receive the newly proposes block or pre-prepare message
		case preprepareMsg:
			if sm.verifyBlock(inputBlock) {
				ret, err := sm.composePrepareMsg(inputBlock)
				if err != nil {
					return nil, noAction, noType, noMsg, consensus.Idle, err
				}
				return ret, broadcastMsg, header, prepareMsg, consensus.Preprepared, nil
			} else {
				err = errors.New("the proposed block is illegal")
				return sm.proposeImpeachBlock(), insertBlock, block, impeachPrepareMsg, consensus.ImpeachPreprepared, err
			}

		// Stay in consensus.Idle state and insert an impeachment block when receiving an impeach validate message
		case impeachValidateMsg:
			return inputBlock, insertBlock, block, noMsg, consensus.Idle, nil

		// Stay in consensus.Idle state if the validator collects 2f+1 impeach commit messages
		case impeachCommitMsg:
			if sm.impeachCommitCertificate(inputHeader) {
				return sm.composeImpeachValidateMsg(inputHeader), broadcastAndInsertBlock, block, impeachValidateMsg, consensus.Idle, nil
			} else {
				sm.impeachCommitMsgPlus(inputHeader)
				return inputHeader, noAction, noType, noMsg, consensus.Idle, nil
			}

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case impeachPrepareMsg:
			if sm.impeachPrepareCertificate(inputHeader) {
				return inputHeader, broadcastMsg, header, impeachCommitMsg, consensus.ImpeachPrepared, nil
			} else {
				sm.impeachPrepareMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.Idle, nil
			}

		// Transit to impeach pre-prepared state if the timers expires (receiving a impeach pre-prepared message),
		// then generate the impeachment block and broadcast the impeach prepare massage
		case impeachPreprepareMsg:
			return sm.proposeImpeachBlock(), broadcastMsg, block, impeachPrepareMsg, consensus.ImpeachPreprepared, nil
		}
		err = errors.New("not a proper input for consensus.Idle state")

	// The case of pre-prepared state
	case consensus.Preprepared:
		switch msg {
		// Jump to committed state if receive a validate message
		case validateMsg:
			return inputBlock, insertBlock, block, noMsg, consensus.Idle, nil

		// Jump to committed state if receive 2f+1 commit messages
		case commitMsg:
			if sm.commitCertificate(inputHeader) {
				return sm.composeValidateMsg(inputHeader), broadcastAndInsertBlock, block, validateMsg, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				sm.commitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.Preprepared, nil
			}
		// Convert to consensus.Prepared state if collect prepare certificate
		case prepareMsg:
			if sm.prepareCertificate(inputHeader) {
				ret, err := sm.composeCommitMsg(inputHeader)
				if err != nil {
					return nil, noAction, noType, noMsg, consensus.Preprepared, nil
				}
				return ret, broadcastMsg, header, commitMsg, consensus.Prepared, nil
			} else {
				// Add one to the counter of prepare messages
				sm.prepareMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.Preprepared, nil
			}
		case impeachValidateMsg:
			return inputBlock, insertBlock, block, noMsg, consensus.Idle, nil

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case impeachCommitMsg:
			if sm.impeachCommitCertificate(inputHeader) {
				return sm.composeImpeachValidateMsg(inputHeader), broadcastAndInsertBlock, block, impeachValidateMsg, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				sm.commitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.Idle, nil
			}

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case impeachPrepareMsg:
			if sm.impeachPrepareCertificate(inputHeader) {
				return inputHeader, broadcastMsg, header, impeachCommitMsg, consensus.ImpeachPrepared, nil
			} else {
				sm.impeachPrepareMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.Preprepared, nil
			}

		case impeachPreprepareMsg:
			return sm.proposeImpeachBlock(), broadcastMsg, block, impeachPrepareMsg, consensus.ImpeachPreprepared, nil

		}
		err = errors.New("not a proper input for pre-prepared state")

	// The case of consensus.Prepared stage
	case consensus.Prepared:
		switch msg {
		// Jump to committed state if receive a validate message
		case validateMsg:
			return inputBlock, insertBlock, block, noMsg, consensus.Idle, nil

		// convert to committed state if collects commit certificate
		case commitMsg:
			if sm.commitCertificate(inputHeader) {
				return sm.composeValidateMsg(inputHeader), broadcastAndInsertBlock, block, validateMsg, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				sm.commitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.Preprepared, nil
			}

		// Transit to consensus.Idle state to insert impeach block
		case impeachValidateMsg:
			return inputBlock, insertBlock, block, noMsg, consensus.Idle, nil

		// Transit to consensus.Idle state to committed state if receive 2f+1 commit messages
		case impeachCommitMsg:
			if sm.impeachCommitCertificate(inputHeader) {
				return sm.composeImpeachValidateMsg(inputHeader), broadcastAndInsertBlock, block, impeachValidateMsg, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				sm.impeachCommitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.Prepared, nil
			}

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case impeachPrepareMsg:
			if sm.impeachPrepareCertificate(inputHeader) {
				return inputHeader, broadcastMsg, header, impeachCommitMsg, consensus.ImpeachPrepared, nil
			} else {
				sm.impeachPrepareMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.Prepared, nil
			}

		case impeachPreprepareMsg:
			return sm.proposeImpeachBlock(), broadcastMsg, block, impeachPrepareMsg, consensus.ImpeachPreprepared, nil
		}
		err = errors.New("not a proper input for consensus.Prepared state")

	case consensus.ImpeachPreprepared:
		switch msg {
		// Transit to consensus.Idle state when receiving impeach validate message
		case impeachValidateMsg:
			return inputBlock, insertBlock, block, noMsg, consensus.Idle, nil

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case impeachCommitMsg:
			if sm.impeachCommitCertificate(inputHeader) {
				return sm.composeImpeachValidateMsg(inputHeader), broadcastAndInsertBlock, block, impeachValidateMsg, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				sm.impeachCommitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.ImpeachPreprepared, nil
			}

		// Transit to impeach consensus.Prepared state if it collects 2f+1 impeach prepare messages
		case impeachPrepareMsg:
			if sm.impeachPrepareCertificate(inputHeader) {
				return inputHeader, broadcastMsg, header, impeachCommitMsg, consensus.ImpeachPrepared, nil
			} else {
				sm.impeachPrepareMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.ImpeachPreprepared, nil
			}
		}

	case consensus.ImpeachPrepared:
		switch msg {
		// Transit to consensus.Idle state when receiving impeach validate message
		case impeachValidateMsg:
			return inputBlock, insertBlock, block, noMsg, consensus.Idle, nil

		// Stay in consensus.Idle state to committed state if receive 2f+1 commit messages
		case impeachCommitMsg:
			if sm.impeachCommitCertificate(inputHeader) {
				return sm.composeImpeachValidateMsg(inputHeader), broadcastAndInsertBlock, block, impeachValidateMsg, consensus.Idle, nil
			} else {
				// Add one to the counter of commit messages
				sm.impeachCommitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, consensus.ImpeachPrepared, nil
			}

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

	return nil, noAction, noType, noMsg, state, err
}
