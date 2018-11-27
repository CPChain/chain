package dpor

//Type enumerator for FSM action
type action int64

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
type msgCode int64

const (
	preprepareMsg msgCode = iota
	prepareMsg
	commitMsg
	validateMsg
)

//Type enumerator for FSM states
type state int64

const (
	idle state = iota
	preprepared
	prepared
	committed
	inserting
)

func FSM(input interface{}, inputType dataType, msg msgCode, s state) (interface{}, action, dataType, msgCode, error) {
	return nil, 0, 0, 0, nil
}
