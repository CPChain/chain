package consensus

import "github.com/ethereum/go-ethereum/common"

// committee network

// CommitteeHandler is an interface used to do network building and related thing.
type CommitteeHandler interface {
	// DialAll dials remote signers.
	DialAll()

	// Disconnect disconnects all.
	Disconnect()

	// UpdateSigners updates OverlayHandler's remoteSigners.
	UpdateSigners(epochIdx uint64, signers []common.Address) error
}
