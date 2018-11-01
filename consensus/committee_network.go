package consensus

import "github.com/ethereum/go-ethereum/common"

// committee network

// CommitteeHandler is an interface used to do network building and related thing.
type CommitteeHandler interface {
	// DialAll dials remote signers.
	DialAll()

	// Disconnect disconnects all.
	Disconnect()

	// UpdateRemoteSigners updates OverlayHandler's remoteSigners.
	UpdateRemoteSigners(epochIdx uint64, signers []common.Address) error
}
