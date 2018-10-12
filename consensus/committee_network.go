package consensus

import "github.com/ethereum/go-ethereum/common"

// committee network

// CommitteeNetworkHandler is an interface used to do network building and related thing.
type CommitteeNetworkHandler interface {
	// Connect connects remote signers.
	Connect()

	// Disconnect disconnects all.
	Disconnect()

	// UpdateRemoteSigners updates OverlayHandler's remoteSigners.
	UpdateRemoteSigners(epochIdx uint64, signers []common.Address) error
}
