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
type FsmState uint8

const (
	idle FsmState = iota
	preprepared
	prepared
	//committed
	//inserting
	impeachPreprepared
	impeachPrepared
	//impeachCommited
)

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
	signers, err := sm.service.EcrecoverSigs(h, consensus.Committing)
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
	signers, err := sm.service.EcrecoverSigs(h, consensus.Preparing)
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

// It returns true it collects 2f+1 impeach prepare messages
func impeachPrepareCertificate(h *types.Header) bool {
	//TODO @shiyc implement it
	return true
}

func impeachPrepareMsgPlus(h *types.Header) {
	//TODO @shiyc
}

func composeImpeachCommitMsg(h *types.Header) *types.Header {
	return h
}

func impeachCommitCertificate(h *types.Header) bool {
	//TODO @shiyc implement it
	return true
}

func impeachCommitMsgPlus(h *types.Header) {
	//TODO @shiyc implement it
}

// Fsm is the finite state machine for a validator, to output the correct state given on current state and inputs
func (sm *DporSm) Fsm(input interface{}, inputType dataType, msg msgCode, state FsmState) (interface{}, action, dataType, msgCode, FsmState, error) {
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
		return nil, noAction, noType, noMsg, idle, err
	}

	switch state {
	// The case of idle state
	case idle:
		switch msg {
		// Stay in idle state if receives validate message, and we should insert the block
		case validateMsg:
			return inputBlock, insertBlock, block, noMsg, idle, nil

		// Jump to committed state if receive 2f+1 commit messages
		case commitMsg:
			if sm.commitCertificate(inputHeader) {
				return sm.composeValidateMsg(inputHeader), broadcastAndInsertBlock, block, validateMsg, idle, nil
			} else {
				// Add one to the counter of commit messages
				sm.commitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, idle, nil
			}

		// Jump to prepared state if receive 2f+1 prepare message
		case prepareMsg:
			if sm.prepareCertificate(inputHeader) {
				ret, err := sm.composeCommitMsg(inputHeader)
				if err != nil {
					return nil, noAction, noType, noMsg, idle, err
				}
				return ret, broadcastMsg, header, commitMsg, prepared, nil
			} else {
				// Add one to the counter of prepare messages
				sm.prepareMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, idle, nil
			}

		// For the case that receive the newly proposes block or pre-prepare message
		case preprepareMsg:
			if sm.verifyBlock(inputBlock) {
				ret, err := sm.composePrepareMsg(inputBlock)
				if err != nil {
					return nil, noAction, noType, noMsg, idle, err
				}
				return ret, broadcastMsg, header, prepareMsg, preprepared, nil
			} else {
				err = errors.New("the proposed block is illegal")
				return sm.proposeImpeachBlock(), insertBlock, block, impeachPrepareMsg, impeachPreprepared, err
				//TODO: return an impeach block
			}

		// Transit to impeach committed state if the validator collects 2f+1 impeach commit messages
		case impeachCommitMsg:
			if impeachCommitCertificate(inputHeader) {
				return inputHeader, broadcastMsg, header, impeachCommitMsg, idle, nil
			} else {
				impeachCommitMsgPlus(inputHeader)
				return inputHeader, noAction, noType, noMsg, idle, nil
			}

		// Transit to impeach prepared state if it collects 2f+1 impeach prepare messages
		case impeachPrepareMsg:
			if impeachPrepareCertificate(inputHeader) {
				return inputHeader, broadcastMsg, header, impeachCommitMsg, impeachPrepared, nil
			} else {
				impeachPrepareMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, idle, nil
			}

		// Transit to impeach pre-prepared state if the timers expires (receiving a impeach pre-prepared message),
		// then generate the impeachment block and broadcast the impeach prepare massage
		case impeachPreprepareMsg:
			return sm.proposeImpeachBlock(), broadcastMsg, block, impeachPrepareMsg, impeachPreprepared, nil
		}
		err = errors.New("not a proper input for idle state")

	// The case of pre-prepared state
	case preprepared:
		switch msg {
		// Jump to committed state if receive a validate message
		case validateMsg:
			return inputBlock, insertBlock, block, noMsg, idle, nil

		// Jump to committed state if receive 2f+1 commit messages
		case commitMsg:
			if sm.commitCertificate(inputHeader) {
				return sm.composeValidateMsg(inputHeader), broadcastAndInsertBlock, block, validateMsg, idle, nil
			} else {
				// Add one to the counter of commit messages
				sm.commitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, preprepared, nil
			}
		// Convert to prepared state if collect prepare certificate
		case prepareMsg:
			if sm.prepareCertificate(inputHeader) {
				ret, err := sm.composeCommitMsg(inputHeader)
				if err != nil {
					return nil, noAction, noType, noMsg, preprepared, nil
				}
				return ret, broadcastMsg, header, commitMsg, prepared, nil
			} else {
				// Add one to the counter of prepare messages
				sm.prepareMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, idle, nil
			}
		}
		err = errors.New("not a proper input for pre-prepared state")

	// The case of prepared stage
	case prepared:
		switch msg {
		// Jump to committed state if receive a validate message
		case validateMsg:
			return inputBlock, insertBlock, block, noMsg, idle, nil

		// convert to committed state if collects commit certificate
		case commitMsg:
			if sm.commitCertificate(inputHeader) {
				return sm.composeValidateMsg(inputHeader), broadcastAndInsertBlock, block, validateMsg, idle, nil
			} else {
				// Add one to the counter of commit messages
				sm.commitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, preprepared, nil
			}
		}
		err = errors.New("not a proper input for prepared state")

		// Broadcast a validate message and then go back to idle state
		//case committed:
		///return sm.composeValidateMsg(inputHeader), broadcastAndInsertBlock, block, validateMsg, idle, nil
		// Broadcast a validate message and then go back to idle state
		//case committed:
		//	return composeValidateMsg(inputHeader), broadcastAndInsertBlock, block, validateMsg, idle, nil

		// Insert the block and go back to idle state
		//case inserting:
		//	return inputBlock, insertBlock, block, noMsg, idle, nil
	}

	return nil, noAction, noType, noMsg, state, err
}
