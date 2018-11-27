package dpor

import (
	"errors"

	"fmt"

	"bitbucket.org/cpchain/chain/types"
)

//Type enumerator for FSM action
type action uint8

const (
	broadcastMsg action = iota
	insertBlock
)

//Type enumerator for FSM output
type dataType uint8

const (
	header dataType = iota
	block
	emptyBlock
)

//Type enumerator for FSM message type
type msgCode uint8

const (
	preprepareMsg msgCode = iota
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
	//TODO: @shiyc
}

//Fsm is the finite state machine for a validator, to output the correct state given on current state and inputs
func Fsm(input interface{}, inputType dataType, msg msgCode, state FsmState) (interface{}, action, dataType, msgCode, error) {
	var inputHeader *types.Header
	var inputBlock *types.Block
	var err error
	var ret interface{}

	switch inputType {
	case header:
		inputHeader = input.(*types.Header)
	case block:
		inputBlock = input.(*types.Block)
	case emptyBlock:
		inputBlock = input.(*types.Block)
	default:
		err = errors.New("an unexpected input data type")
		return nil, 0, 0, 0, err
	}
	switch state {
	case idle:
		if verifyBlock(inputBlock) {
			fmt.Println("hao!")
		} else {
			err = errors.New("the proposed block is illegal")

			return ret, insertBlock, block, emptyPrepareMsg, err
			//TODO: return a empty block
		}

	}

	return nil, 0, 0, 0, nil
}
