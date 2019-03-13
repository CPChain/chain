package backend

import (
	"github.com/ethereum/go-ethereum/common"
)

// RemoteProposer represents a remote proposer waiting to be connected.
type RemoteProposer struct {
	*RemoteSigner
}

// NewRemoteProposer creates a new remote proposer
func NewRemoteProposer(address common.Address) *RemoteProposer {
	return &RemoteProposer{
		RemoteSigner: NewRemoteSigner(address),
	}
}
