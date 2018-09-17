package dpor

import "github.com/ethereum/go-ethereum/common"

// overlay network

// OverlayCallback is an interface used to do network building and related thing.
type OverlayCallback interface {

	// Callback handles all.
	Callback()

	// UpdateRemoteSigners updates OverlayCallback's remoteSigners.
	UpdateRemoteSigners(viewIdx uint64, signers []common.Address) error

	// FetchPubKey fetches remote peers' public keys.
	FetchPubKey() error

	// UpdateNodeID updates self NodeID to contract.
	UpdateNodeID() error

	// FetchNodeID fetches remote peers' NodeIDs from contract.
	FetchNodeID() error

	// DialRemote dials remote peers with their NodeID.
	DialRemote() error
}
