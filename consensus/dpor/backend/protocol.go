package backend

import (
	"fmt"

	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/p2p"
)

const (
	// ProtocolName protocol name
	ProtocolName = "dpor"

	// ProtocolVersion protocol verion
	ProtocolVersion = 65

	// ProtocolLength protocol length, max msg code
	ProtocolLength = 100
)

const (

	// Protocol messages belonging to cpc/01

	// NewSignerMsg is a msg code used for network building
	NewSignerMsg = 0x42

	// PbftMsgOutset is not a msg code, just used for msg code comparing
	PbftMsgOutset = 0x42

	// PreprepareBlockMsg is Preprepare phrase msg code
	PreprepareBlockMsg = 0x43

	// PrepareHeaderMsg is Prepare phrase msg code
	PrepareHeaderMsg = 0x44

	// CommitHeaderMsg is Commit phrase msg code
	CommitHeaderMsg = 0x45

	// PreprepareImpeachBlockMsg is Preprepare phrase msg code for empty block
	PreprepareImpeachBlockMsg = 0x46

	// PrepareImpeachHeaderMsg is Prepare phrase msg code for empty header
	PrepareImpeachHeaderMsg = 0x47

	// CommitImpeachHeaderMsg is Commit phrase msg code for empty header
	CommitImpeachHeaderMsg = 0x48

	ValidateBlockMsg = 0x49

	ValidateImpeachBlockMsg = 0x50
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

type SignerStatusData struct {
	ProtocolVersion uint32
	Mac             string
	Sig             []byte
	// Address         common.Address
}

func errResp(code errCode, format string, v ...interface{}) error {
	return fmt.Errorf("%v - %v", code, fmt.Sprintf(format, v...))
}

func IsSyncMsg(msg p2p.Msg) bool {
	return msg.Code < PbftMsgOutset
}

func IsDporMsg(msg p2p.Msg) bool {
	return msg.Code >= PbftMsgOutset
}

// RecoverBlockFromMsg recovers a block from a p2p msg
func RecoverBlockFromMsg(msg p2p.Msg, p interface{}) (*types.Block, error) {
	// recover the block
	var block *types.Block
	if err := msg.Decode(&block); err != nil {
		return nil, errResp(ErrDecode, "%v: %v", msg, err)
	}
	block.ReceivedAt = msg.ReceivedAt
	block.ReceivedFrom = p

	return block, nil
}

// RecoverHeaderFromMsg recovers a header from a p2p msg
func RecoverHeaderFromMsg(msg p2p.Msg, p interface{}) (*types.Header, error) {
	// retrieve the header
	var header *types.Header
	if err := msg.Decode(&header); err != nil {
		return nil, errResp(ErrDecode, "msg %v: %v", msg, err)
	}
	return header, nil
}
