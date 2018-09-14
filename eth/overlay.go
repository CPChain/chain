package eth

import "github.com/ethereum/go-ethereum/common"

// overlay network

// OverlayCallback is an interface used to do network building and related thing.
type OverlayCallback interface {
	// FetchPubKey fetches remote peer's public key from contract.
	FetchPubKey(remoteAddress common.Address) (pubkey []byte, err error)

	// UpdateNodeID updates self NodeID to contract.
	UpdateNodeID(ownNodeID string) error

	// FetchNodeID fetches remote peer's NodeID from contract.
	FetchNodeID() (remoteNodeID string, err error)

	// DialRemote dials remote peer with given NodeID.
	DialRemote(remoteNodeID string, ownAddress common.Address) (err error)
}

// BasicOverlayCallback implements OverlayCallback
type BasicOverlayCallback struct {
}

// FetchPubKey implements OverlayCallback.FetchPubKey
func (oc *BasicOverlayCallback) FetchPubKey(remoteAddress common.Address) (pubkey []byte, err error) {
	panic("not implemented")
}

// UpdateNodeID implements OverlayCallback.UpdateNodeID
func (oc *BasicOverlayCallback) UpdateNodeID(ownNodeID string) error {
	panic("not implemented")
}

// FetchNodeID implements OverlayCallback.FetchNodeID
func (oc *BasicOverlayCallback) FetchNodeID() (remoteNodeID string, err error) {
	panic("not implemented")
}

// DialRemote implements OverlayCallback.DialRemote
func (oc *BasicOverlayCallback) DialRemote(remoteNodeID string, ownAddress common.Address) (err error) {
	panic("not implemented")
}
