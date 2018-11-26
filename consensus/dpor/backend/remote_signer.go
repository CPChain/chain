package backend

import (
	"fmt"
	"sync"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
)

const (
	maxQueuedPendingBlocks      = 8
	maxQueuedPendingBlockHashes = 8
	maxQueuedSigs               = 8

	handshakeTimeout = 5 * time.Second
)

type RemoteSigner struct {
	*p2p.Peer
	rw      p2p.MsgReadWriter
	version int

	epochIdx uint64
	pubkey   []byte
	nodeID   string
	address  common.Address

	dialed        bool // bool to show if i already connected to this signer.
	pubkeyFetched bool
	nodeIDFetched bool
	nodeIDUpdated bool // bool to show if i updated my nodeid encrypted with this signer's pubkey to the contract.

	lock sync.RWMutex
}

// RemoteProposer represents a remote proposer waiting to be connected.
type RemoteProposer struct {
	*RemoteSigner
}

// NewRemoteSigner creates a new remote signer
func NewRemoteSigner(epochIdx uint64, address common.Address) *RemoteSigner {
	return &RemoteSigner{
		epochIdx: epochIdx,
		address:  address,
	}

}

// NewRemoteProposer creates a new remote proposer
func NewRemoteProposer(epochIdx uint64, address common.Address) *RemoteProposer {
	return &RemoteProposer{
		RemoteSigner: NewRemoteSigner(epochIdx, address),
	}
}

// AddStatic adds remote validator as a static peer
func (s *RemoteSigner) AddStatic(srv *p2p.Server) error {

	rawurl := fmt.Sprintf("enode://%v@%v", s.ID().String(), s.RemoteAddr().String())
	nodeId, err := discover.ParseNode(rawurl)
	if err != nil {
		return err
	}
	srv.AddPeer(nodeId)
	return nil
}

func (s *RemoteSigner) disconnect(server *p2p.Server) error {
	s.lock.Lock()
	nodeID := s.nodeID
	s.lock.Unlock()

	node, err := discover.ParseNode(nodeID)
	if err != nil {
		return err
	}
	server.RemovePeer(node)
	return nil
}

// SetPeer sets a p2p peer
func (s *RemoteSigner) SetPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter) error {
	s.lock.Lock()
	defer s.lock.Unlock()

	s.version, s.Peer, s.rw = version, p, rw

	return nil
}

// ValidatorHandshake tries to handshake with remote validator
func ValidatorHandshake(p *p2p.Peer, rw p2p.MsgReadWriter, coinbase common.Address, verifyRemoteValidatorFn VerifyRemoteValidatorFn) (isValidator bool, address common.Address, err error) {
	// Send out own handshake in a new thread
	errc := make(chan error, 2)
	var validatorStatus ValidatorStatusData // safe to read after two values have been received from errc

	go func() {
		err := p2p.Send(rw, NewValidatorMsg, &ValidatorStatusData{
			ProtocolVersion: uint32(ProtocolVersion),
			Address:         coinbase,
		})
		errc <- err
	}()
	go func() {
		isValidator, address, err = ReadValidatorStatus(p, rw, &validatorStatus, verifyRemoteValidatorFn)
		errc <- err
	}()
	timeout := time.NewTimer(handshakeTimeout)
	defer timeout.Stop()
	for i := 0; i < 2; i++ {
		select {
		case err := <-errc:
			if err != nil {
				return false, common.Address{}, err
			}
		case <-timeout.C:
			return false, common.Address{}, p2p.DiscReadTimeout
		}
	}
	return isValidator, address, nil
}

// ReadValidatorStatus reads status of remote validator
func ReadValidatorStatus(p *p2p.Peer, rw p2p.MsgReadWriter, validatorStatus *ValidatorStatusData, verifyValidatorFn VerifyRemoteValidatorFn) (isValidator bool, address common.Address, err error) {
	msg, err := rw.ReadMsg()
	if err != nil {
		return false, common.Address{}, err
	}
	if msg.Code != NewValidatorMsg {
		return false, common.Address{}, errResp(ErrNoStatusMsg, "first msg has code %x (!= %x)", msg.Code, NewValidatorMsg)
	}
	if msg.Size > ProtocolMaxMsgSize {
		return false, common.Address{}, errResp(ErrMsgTooLarge, "%v > %v", msg.Size, ProtocolMaxMsgSize)
	}
	// Decode the handshake and make sure everything matches
	if err := msg.Decode(&validatorStatus); err != nil {
		return false, common.Address{}, errResp(ErrDecode, "msg %v: %v", msg, err)
	}
	if int(validatorStatus.ProtocolVersion) != ProtocolVersion {
		return false, common.Address{}, errResp(ErrProtocolVersionMismatch, "%d (!= %d)", validatorStatus.ProtocolVersion, ProtocolVersion)
	}

	// TODO: this (addr, ...) pair should be signed with its private key.
	// @liuq

	isValidator, err = verifyValidatorFn(validatorStatus.Address)
	return isValidator, validatorStatus.Address, err
}
