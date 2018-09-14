package dpor

import "github.com/ethereum/go-ethereum/common"

// overlay network

// OverlayCallback is an interface used to do network building and related thing.
type OverlayCallback interface {

	// Callback handles all.
	Callback() (err error)

	// FetchPubKey fetches remote peer's public key from contract.
	FetchPubKey(remoteAddress common.Address) (pubkey []byte, err error)

	// UpdateNodeID updates self NodeID to contract.
	UpdateNodeID(ownNodeID string) error

	// FetchNodeID fetches remote peer's NodeID from contract.
	FetchNodeID() (remoteNodeID string, err error)

	// DialRemote dials remote peer with given NodeID.
	DialRemote(remoteNodeID string, ownAddress common.Address) (err error)
}
