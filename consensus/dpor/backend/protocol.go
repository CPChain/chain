package backend

import (
	"fmt"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

const (

	// Protocol messages belonging to cpc/01

	// NewSignerMsg is a msg code used for committee network building
	NewSignerMsg = 0x42

	// PbftMsgOutSet is not a msg code, just used for msg code comparing
	PbftMsgOutSet = 0x43

	// PrepreparePendingBlockMsg is Preprepare phrase msg code
	PrepreparePendingBlockMsg = 0x43

	// PrepareSignedHeaderMsg is Prepare phrase msg code
	PrepareSignedHeaderMsg = 0x44

	// CommitSignedHeaderMsg is Commit phrase msg code
	CommitSignedHeaderMsg = 0x45
)

const ProtocolMaxMsgSize = 10 * 1024 * 1024 // Maximum cap on the size of a protocol message

type errCode int

const (
	ErrMsgTooLarge = iota
	ErrDecode
	ErrInvalidMsgCode
	ErrProtocolVersionMismatch
	ErrNetworkIdMismatch
	ErrGenesisBlockMismatch
	ErrNoStatusMsg
	ErrExtraStatusMsg
	ErrSuspendedPeer
)

func (e errCode) String() string {
	return errorToString[int(e)]
}

// XXX change once legacy code is out
var errorToString = map[int]string{
	ErrMsgTooLarge:             "Message too long",
	ErrDecode:                  "Invalid message",
	ErrInvalidMsgCode:          "Invalid message code",
	ErrProtocolVersionMismatch: "Protocol version mismatch",
	ErrNetworkIdMismatch:       "NetworkId mismatch",
	ErrGenesisBlockMismatch:    "Genesis block mismatch",
	ErrNoStatusMsg:             "No status message",
	ErrExtraStatusMsg:          "Extra status message",
	ErrSuspendedPeer:           "Suspended peer",
}

type signerStatusData struct {
	ProtocolVersion uint32
	Address         common.Address
}

func errResp(code errCode, format string, v ...interface{}) error {
	return fmt.Errorf("%v - %v", code, fmt.Sprintf(format, v...))
}

func IsPbftMsg(msg p2p.Msg) bool {
	return msg.Code >= PbftMsgOutSet
}
