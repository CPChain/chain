package eth

import (
	"errors"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/ethclient"
	"github.com/ethereum/go-ethereum/log"
)

const (
	// RSAPubkeyLength is the length of the RSA public key used to encrypt nodeID.
	RSAPubkeyLength = 512
)

// NodeID is a string of the rawurl of enodeid, an example is
// "enode://a979fb575495b8d6db44f750317d0f4622bf4c2aa3365d6af7c284339968eef29b69ad0dce72a4d8db5ebb4968de0e3bec910127f134779fbcb0cb6d3331163c@52.16.188.185:30303"
type NodeID string

// Pubkey is a byte array to represents a RSA public key.
type Pubkey [RSAPubkeyLength]byte

// RemoteSigner represents a remote signer waiting to be connected and communicate with.
type RemoteSigner struct {
	epochIdx  uint64
	pubkey    Pubkey
	nodeID    NodeID
	address   common.Address
	updated   bool // bool to show if i updated my nodeid encrypted with this signer's pubkey to the contract.
	connected bool // bool to show if i already connected to this signer.
}

// NewRemoteSigner creates a new NewRemoteSigner with given view idx and address.
func NewRemoteSigner(epochIdx uint64, address common.Address) *RemoteSigner {
	return &RemoteSigner{
		epochIdx:  epochIdx,
		address:   address,
		updated:   false,
		connected: false,
	}
}

// fetchPubkey fetches the public key of the remote signer from the contract.
func (rs *RemoteSigner) fetchPubkey() (Pubkey, error) {
	panic("not implemented")
}

// fetchNodeID fetches the node id of the remote signer encrypted with my public key, and decrypts it with my private key.
func (rs *RemoteSigner) fetchNodeID() (NodeID, error) {
	panic("not implemented")
}

// updateNodeID encrypts my node id with this remote signer's public key and update to the contract.
func (rs *RemoteSigner) updateNodeID(nodeID NodeID) error {
	panic("not implemented")
}

// BasicOverlayCallback implements OverlayCallback
type BasicOverlayCallback struct {
	peers *peerSet

	epochIdx uint64

	ownNodeID  NodeID
	ownPubkey  Pubkey
	ownAddress common.Address

	remoteSigners []*RemoteSigner
}

// NewBasicOverlayCallback creates a BasicOverlayCallback instance
func NewBasicOverlayCallback(peers *peerSet, epochIdx uint64, epochLength uint64, ownNodeID NodeID, ownPubkey Pubkey, ownAddress common.Address) *BasicOverlayCallback {
	return &BasicOverlayCallback{
		peers:         peers,
		epochIdx:      epochIdx,
		ownNodeID:     ownNodeID,
		ownPubkey:     ownPubkey,
		ownAddress:    ownAddress,
		remoteSigners: make([]*RemoteSigner, epochLength-1),
	}
}

// UpdateRemoteSigners updates BasicOverlayCallback's remoteSigners.
func (oc *BasicOverlayCallback) UpdateRemoteSigners(epochIdx uint64, signers []common.Address) error {
	oc.epochIdx = epochIdx

	if len(signers) != len(oc.remoteSigners) {
		return errors.New("error length of signer")
	}
	for _, signer := range signers {
		s := NewRemoteSigner(epochIdx, signer)
		oc.remoteSigners = append(oc.remoteSigners, s)
	}
	return nil
}

// Callback implements OverlayCallback.Callback
func (oc *BasicOverlayCallback) Callback(ethClient *ethclient.Client) {

	// TODO: add lock, go rountine this! Liu Qian
	err := oc.FetchPubKey()
	if err != nil {
		log.Warn("error when fetching remote signers' pubkey", "err", "err")
	}

	err = oc.UpdateNodeID()
	if err != nil {
		log.Warn("error when updating self nodeID encrypted with remote signers' pubkey", "err", "err")
	}

	err = oc.FetchNodeID()
	if err != nil {
		log.Warn("error when fetching remote signers' nodeIDs", "err", "err")
	}

	err = oc.DialRemote()
	if err != nil {
		log.Warn("error when dialing to remote signers", "err", "err")
	}
}

// FetchPubKey implements OverlayCallback.FetchPubKey
func (oc *BasicOverlayCallback) FetchPubKey() error {

	for idx, signer := range oc.remoteSigners {
		if len(signer.pubkey) > 0 {
			log.Debug("already fetched pubkey of", "address", signer.address)
			log.Debug("already fetched pubkey ", "pubkey", signer.pubkey)
			continue
		}
		pubkey, err := signer.fetchPubkey()
		if err != nil {
			log.Warn("error when fetch pubkey of", "address", signer.address)
			log.Warn("error when fetch pubkey ", "error", err)
			continue
			// return err
		}
		oc.remoteSigners[idx].pubkey = pubkey
		log.Debug("fetched pubkey of", "address", signer.address)
		log.Debug("fetched pubkey ", "pubkey", signer.pubkey)
	}
	return nil
}

// UpdateNodeID implements OverlayCallback.UpdateNodeID
func (oc *BasicOverlayCallback) UpdateNodeID() error {
	for idx, signer := range oc.remoteSigners {
		if len(signer.pubkey) == 0 {
			continue
		}
		if signer.updated {
			continue
		}
		err := signer.updateNodeID(oc.ownNodeID)
		if err != nil {
			log.Warn("error when update self nodeID encrypted with remote signer's public", "address", signer.address)
			log.Warn("error", "error", err)
			continue
			// return err
		}
		oc.remoteSigners[idx].updated = true
	}

	return nil
}

// FetchNodeID implements OverlayCallback.FetchNodeID
func (oc *BasicOverlayCallback) FetchNodeID() error {
	for idx, signer := range oc.remoteSigners {
		if len(signer.nodeID) > 0 {
			continue
		}
		nodeID, err := signer.fetchNodeID()
		if err != nil {
			log.Warn("error when update self nodeID encrypted with remote signer's public", "address", signer.address)
			log.Warn("error", "error", err)
			continue
			// return err

		}
		oc.remoteSigners[idx].nodeID = nodeID
	}

	return nil
}

// DialRemote implements OverlayCallback.DialRemote
func (oc *BasicOverlayCallback) DialRemote() (err error) {
	panic("not implemented")
}
