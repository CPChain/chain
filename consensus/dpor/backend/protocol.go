package backend

import (
	"fmt"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

const (
	// ProtocolName protocol name
	ProtocolName = "dpor"

	// ProtocolVersion protocol verion
	ProtocolVersion = 1

	// ProtocolLength protocol length, max msg code
	ProtocolLength = 70
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

// ProtocolMaxMsgSize Maximum cap on the size of a protocol message
const ProtocolMaxMsgSize = 10 * 1024 * 1024

type errCode int

const (
	// ErrMsgTooLarge is returned if msg if too large
	ErrMsgTooLarge = iota

	// ErrDecode is returned if decode failed
	ErrDecode

	// ErrInvalidMsgCode is returned if msg code is invalid
	ErrInvalidMsgCode

	// ErrProtocolVersionMismatch is returned if protocol version is not matched when handshaking
	ErrProtocolVersionMismatch

	// ErrNetworkIdMismatch is returned if networkid is not matched when handshaking
	ErrNetworkIdMismatch

	// ErrGenesisBlockMismatch is returned if genesis block is different from remote signer
	ErrGenesisBlockMismatch

	// ErrNoStatusMsg is returned if failed when reading status msg
	ErrNoStatusMsg

	// ErrExtraStatusMsg is returned if failed when extracting status msg
	ErrExtraStatusMsg

	// ErrSuspendedPeer is returned if remote signer is dead
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

// IsPbftMsg checks if a msg is pbft msg
func IsPbftMsg(msg p2p.Msg) bool {
	return msg.Code >= PbftMsgOutSet
}
