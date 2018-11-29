package dpor

import (
	"errors"

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
	emptyBlock
)

//Type enumerator for FSM message type
type msgCode uint8

const (
	noMsg msgCode = iota
	preprepareMsg
	prepareMsg
	commitMsg
	validateMsg
	emptyPrepareMsg
	emptyCommitMsg
	emptyValidateMsg
)

//Type enumerator for FSM states
type FsmState uint8

const (
	idle FsmState = iota
	preprepared
	prepared
	committed
	inserting
	impeachmentPrepared
	impeachment
)

//verifyBlock is a func to verify whether the block is legal
func verifyBlock(block *types.Block) bool {
	return true
	//TODO: @shiyc implement it
}

// commitCertificate is true if the validator has collected 2f+1 commit messages
func commitCertificate(h *types.Header) bool {
	return true
	//TODO: @shiyc implement it
}

//composeValidateMsg is to return the validate message, which is the proposed block or empty block
func composeValidateMsg(h *types.Header) *types.Block {
	return
	//TODO: @shiyc implement it
}

//Add one to the counter of commit messages
func commitMsgPlus(h *types.Header) {
	//TODO: @shiyc implement it

}

func composeCommitMsg(h *types.Header) *types.Header {
	return h
	//TODO: @shiyc implement it
}

//prepareCertificate is true if the validator has collects 2f+1 prepare messages
func prepareCertificate(h *types.Header) bool {
	return true
	//TODO: @shiyc implement it
}

//Add one to the counter of prepare messages
func prepareMsgPlus(h *types.Header) {
	//TODO: @shiyc implement it
}

func composePrepareMsg(h *types.Block) *types.Header {
	return h.Header()
}

//It is used to propose an empty block
func proposeEmptyBlock() *types.Block {
	var b *types.Block
	return b
}

// Fsm is the finite state machine for a validator, to output the correct state given on current state and inputs
func Fsm(input interface{}, inputType dataType, msg msgCode, state FsmState) (interface{}, action, dataType, msgCode, FsmState, error) {
	var inputHeader *types.Header
	var inputBlock *types.Block
	var err error

	// Determine the input is a header or a block
	switch inputType {
	case header:
		inputHeader = input.(*types.Header)
	case block:
		inputBlock = input.(*types.Block)
	case emptyBlock:
		inputBlock = input.(*types.Block)
	default:
		err = errors.New("an unexpected input data type")
		return nil, noAction, noType, noMsg, idle, err
	}

	switch state {
	// The case of idle state
	case idle:
		switch msg {
		// Jump to inserting state if receives validate message
		case validateMsg:
			return inputBlock, noAction, noType, noMsg, inserting, nil

		// Jump to committed state if receive 2f+1 commit messages
		case commitMsg:
			if commitCertificate(inputHeader) {
				return composeValidateMsg(inputHeader), broadcastMsg, block, validateMsg, committed, nil
			} else {
				// Add one to the counter of commit messages
				commitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, idle, nil
			}

		// Jump to prepared state if receive 2f+1 prepare message
		case prepareMsg:
			if prepareCertificate(inputHeader) {
				return composeCommitMsg(inputHeader), broadcastMsg, header, commitMsg, prepared, nil
			} else {
				// Add one to the counter of prepare messages
				prepareMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, idle, nil
			}

		// For the case that receive the newly proposes block or pre-prepare message
		case preprepareMsg:
			if verifyBlock(inputBlock) {
				return composePrepareMsg(inputBlock), broadcastMsg, header, prepareMsg, preprepared, nil
			} else {
				err = errors.New("the proposed block is illegal")
				return proposeEmptyBlock(), insertBlock, block, emptyPrepareMsg, idle, err
				//TODO: return an empty block
			}
		}
		err = errors.New("not a proper input for idle state")

	// The case of pre-prepared state
	case preprepared:
		switch msg {
		// Jump to inserting state if receive a validate message
		case validateMsg:
			return inputBlock, noAction, noType, noMsg, inserting, nil

			// Jump to committed state if receive 2f+1 commit messages
		case commitMsg:
			if commitCertificate(inputHeader) {
				return composeValidateMsg(inputHeader), broadcastMsg, block, validateMsg, committed, nil
			} else {
				// Add one to the counter of commit messages
				commitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, preprepared, nil
			}
		// Convert to prepared state if collect prepare certificate
		case prepareMsg:
			if prepareCertificate(inputHeader) {
				return composeCommitMsg(inputHeader), broadcastMsg, header, commitMsg, prepared, nil
			} else {
				// Add one to the counter of prepare messages
				prepareMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, idle, nil
			}
		}
		err = errors.New("not a proper input for pre-prepared state")

	// The case of prepared stage
	case prepared:
		switch msg {
		// Jump to inserting state if receive a validate message
		case validateMsg:
			return inputBlock, noAction, noType, noMsg, inserting, nil

		// convert to committed state if collects commit certificate
		case commitMsg:
			if commitCertificate(inputHeader) {
				return composeValidateMsg(inputHeader), broadcastMsg, block, validateMsg, committed, nil
			} else {
				// Add one to the counter of commit messages
				commitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, preprepared, nil
			}
		}
		err = errors.New("not a proper input for prepared state")

	// Broadcast a validate message and then enter inserting state
	case committed:
		return composeValidateMsg(inputHeader), broadcastMsg, block, validateMsg, inserting, nil

	// Insert the block and go back to idle state
	case inserting:
		return inputBlock, insertBlock, block, noMsg, idle, nil
	}

	return nil, noAction, noType, noMsg, state, err
}
