package backend

import (
	"fmt"
	"math/big"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts"
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

	term    uint64
	nodeID  string
	address common.Address

	dialed        bool // bool to show if i already connected to this signer.
	nodeIDFetched bool
	nodeIDUpdated bool // bool to show if i updated my nodeid encrypted with this signer's pubkey to the contract.

	lock sync.RWMutex
}

// NewRemoteSigner creates a new remote signer
func NewRemoteSigner(term uint64, address common.Address) *RemoteSigner {
	return &RemoteSigner{
		term:    term,
		address: address,
	}

}

// SetTerm sets term of signer
func (s *RemoteSigner) SetTerm(term uint64) {
	s.lock.Lock()
	defer s.lock.Unlock()

	s.term = term
}

// GetTerm sets term of signer
func (s *RemoteSigner) GetTerm() uint64 {
	s.lock.RLock()
	defer s.lock.RUnlock()

	return s.term
}

// AddStatic adds remote validator as a static peer
func (s *RemoteSigner) AddStatic(srv *p2p.Server) error {

	rawurl := fmt.Sprintf("enode://%v@%v", s.ID().String(), s.RemoteAddr().String())
	nodeID, err := discover.ParseNode(rawurl)
	if err != nil {
		return err
	}
	srv.AddPeer(nodeID)
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

// Handshake tries to handshake with remote validator
func Handshake(p *p2p.Peer, rw p2p.MsgReadWriter, coinbase common.Address, term uint64, verifyProposerFn VerifyFutureSignerFn, verifyValidatorFn VerifyFutureSignerFn) (isProposer bool, isValidator bool, address common.Address, err error) {
	// Send out own handshake in a new thread
	errc := make(chan error, 2)
	var signerStatus SignerStatusData // safe to read after two values have been received from errc

	go func() {
		err := p2p.Send(rw, NewSignerMsg, &SignerStatusData{
			ProtocolVersion: uint32(ProtocolVersion),
			Address:         coinbase,
			Term:            term,
		})
		errc <- err
	}()
	go func() {
		isProposer, isValidator, address, err = ReadValidatorStatus(p, rw, &signerStatus, verifyProposerFn, verifyValidatorFn)
		errc <- err
	}()
	timeout := time.NewTimer(handshakeTimeout)
	defer timeout.Stop()
	for i := 0; i < 2; i++ {
		select {
		case err := <-errc:
			if err != nil {
				log.Debug("err when handshaking", "err", err)
				return false, false, common.Address{}, err
			}
		case <-timeout.C:
			log.Debug("handshaking time out", "err", err)
			return false, false, common.Address{}, p2p.DiscReadTimeout
		}
	}
	return false, isValidator, address, nil
}

// ReadValidatorStatus reads status of remote validator
func ReadValidatorStatus(p *p2p.Peer, rw p2p.MsgReadWriter, signerStatusData *SignerStatusData, verifyProposerFn VerifyFutureSignerFn, verifyValidatorFn VerifyFutureSignerFn) (isProposer bool, isValidator bool, address common.Address, err error) {
	msg, err := rw.ReadMsg()
	if err != nil {
		return false, false, common.Address{}, err
	}
	if msg.Code != NewSignerMsg {
		return false, false, common.Address{}, errResp(ErrNoStatusMsg, "first msg has code %x (!= %x)", msg.Code, NewSignerMsg)
	}
	if msg.Size > ProtocolMaxMsgSize {
		return false, false, common.Address{}, errResp(ErrMsgTooLarge, "%v > %v", msg.Size, ProtocolMaxMsgSize)
	}
	// Decode the handshake and make sure everything matches
	if err := msg.Decode(&signerStatusData); err != nil {
		return false, false, common.Address{}, errResp(ErrDecode, "msg %v: %v", msg, err)
	}
	if int(signerStatusData.ProtocolVersion) != ProtocolVersion {
		return false, false, common.Address{}, errResp(ErrProtocolVersionMismatch, "%d (!= %d)", signerStatusData.ProtocolVersion, ProtocolVersion)
	}

	// TODO: this (addr, ...) pair should be signed with its private key.
	// @liuq

	isProposer, err = verifyProposerFn(signerStatusData.Address, signerStatusData.Term)
	isValidator, err = verifyValidatorFn(signerStatusData.Address, signerStatusData.Term)
	return isProposer, isValidator, signerStatusData.Address, err
}

// fetchNodeID fetches node id of proposer encrypted with validator's public key
func fetchNodeID(term uint64, proposer common.Address, validator common.Address, contractInstance *dpor.ProposerRegister) ([]byte, error) {
	callOpts := &bind.CallOpts{
		From: validator,
	}
	fmt.Println("contract instance", contractInstance)
	encryptedNodeID, err := contractInstance.GetNodeInfo(callOpts, big.NewInt(int64(term)), proposer)
	if err != nil {
		return nil, err
	}
	return encryptedNodeID, nil
}
