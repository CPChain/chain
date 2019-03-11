package backend

import (
	"sync"

	"github.com/ethereum/go-ethereum/common"
)

// RemoteProposer represents a remote proposer waiting to be connected.
type RemoteProposer struct {
	*RemoteSigner

	nodeID string
	dialed bool // bool to show if i already connected to this signer.

	proposerLock sync.RWMutex
}

// NewRemoteProposer creates a new remote proposer
func NewRemoteProposer(address common.Address) *RemoteProposer {
	return &RemoteProposer{
		RemoteSigner: NewRemoteSigner(address),
	}
}

// Dialed returns if already dialed the remote proposer
func (s *RemoteProposer) Dialed() bool {
	s.proposerLock.RLock()
	defer s.proposerLock.RUnlock()

	return s.dialed
}

// ToggleDialed toggles dialed
func (s *RemoteProposer) ToggleDialed() {
	s.proposerLock.Lock()
	defer s.proposerLock.Unlock()

	s.dialed = !s.dialed
}

func (s *RemoteProposer) getNodeID() string {
	s.proposerLock.RLock()
	defer s.proposerLock.RUnlock()

	return s.nodeID
}

func (s *RemoteProposer) setNodeID(nodeID string) {
	s.proposerLock.Lock()
	defer s.proposerLock.Unlock()

	s.nodeID = nodeID
}
