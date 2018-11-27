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
	noMsg msg = iota
	preprepareMsg
	prepareMsg
	commitMsg
	validateMsg
	emptyPrepareMsg
)

//Type enumerator for FSM states
type FsmState uint8

const (
	idle FsmState = iota
	preprepared
	prepared
	committed
	inserting
	impeachmentPreprepared
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

//composeValidateMsg is to compose a validate message
func composeValidateMsg(h *types.Header) *types.Header {
	return h
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
			return composeValidateMsg(inputHeader), insertBlock, noType, noMsg, inserting, nil
		//
		case commitMsg:
			if commitCertificate(inputHeader) {
				return composeValidateMsg(inputHeader), broadcastMsg, header, validateMsg, inserting, nil
			} else {
				commitMsgPlus(inputHeader)
				return input, noAction, noType, noMsg, idle, nil
			}
		case prepareMsg:
			if prepareCertificate(inputHeader) {
				return
			} else {

			}
		}
		if verifyBlock(inputBlock) {

		} else {
			err = errors.New("the proposed block is illegal")
			return proposeEmptyBlock(), insertBlock, block, emptyPrepareMsg, idle, err
			//TODO: return an empty block
		}

	}

	return nil, doNothing, 0, 0, state, nil
}
