package dpor

import "github.com/ethereum/go-ethereum/common"

// committee network

// CommitteeNetworkHandler is an interface used to do network building and related thing.
type CommitteeNetworkHandler interface {

	// Handle handles all.
	Handle()

	// UpdateRemoteSigners updates OverlayHandler's remoteSigners.
	UpdateRemoteSigners(epochIdx uint64, signers []common.Address) error

	// FetchPubKey fetches remote peers' public keys.
	FetchPubKey() error

	// UpdateNodeID updates self NodeID to contract.
	UpdateNodeID() error

	// FetchNodeID fetches remote peers' NodeIDs from contract.
	FetchNodeID() error

	// DialRemote dials remote peers with their NodeID.
	DialRemote() error
}
