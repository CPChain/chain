package backend

import (
	"errors"
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

var (
	errNilPeer = errors.New("nil Peer in RemoteSigner")
)

const (
	maxQueuedBlocks             = 8
	maxQueuedPendingBlockHashes = 8
	maxQueuedHeaders            = 8

	handshakeTimeout = 5 * time.Second
)

// RemoteSigner represents a remote peer, ether proposer or validator
type RemoteSigner struct {
	*p2p.Peer
	rw      p2p.MsgReadWriter
	version int

	address common.Address

	lock sync.RWMutex
}

// NewRemoteSigner creates a new remote signer
func NewRemoteSigner(address common.Address) *RemoteSigner {
	return &RemoteSigner{
		address: address,
	}

}

func (s *RemoteSigner) EnodeID() string {
	return fmt.Sprintf("enode://%s@%s", s.Peer.ID().String(), s.Peer.RemoteAddr().String())
}

// Coinbase returns remote peer's addr
func (s *RemoteSigner) Coinbase() common.Address {
	s.lock.RLock()
	defer s.lock.RUnlock()

	return s.address
}

// // SetTerm sets term of signer
// func (s *RemoteSigner) SetTerm(term uint64) {
// 	s.lock.Lock()
// 	defer s.lock.Unlock()

// 	s.term = term
// }

// // GetTerm sets term of signer
// func (s *RemoteSigner) GetTerm() uint64 {
// 	s.lock.RLock()
// 	defer s.lock.RUnlock()

// 	return s.term
// }

// AddStatic adds remote validator as a static peer
func (s *RemoteSigner) AddStatic(srv *p2p.Server) error {
	s.lock.RLock()
	defer s.lock.RUnlock()

	if s.Peer != nil {
		rawurl := fmt.Sprintf("enode://%v@%v", s.ID().String(), s.RemoteAddr().String())
		nodeID, err := discover.ParseNode(rawurl)
		if err != nil {
			return err
		}
		srv.AddPeer(nodeID)
		return nil
	}
	log.Warn("remote signer's Peer is nil")
	return errNilPeer
}

func (s *RemoteSigner) disconnect(server *p2p.Server) error {
	rawurl := fmt.Sprintf("enode://%v@%v", s.ID().String(), s.RemoteAddr().String())
	nodeID, err := discover.ParseNode(rawurl)
	if err != nil {
		return err
	}
	server.RemovePeer(nodeID)
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
func Handshake(p *p2p.Peer, rw p2p.MsgReadWriter, mac string, sig []byte, term uint64, futureTerm uint64) (address common.Address, err error) {
	// Send out own handshake in a new thread
	errc := make(chan error, 2)
	var signerStatus SignerStatusData // safe to read after two values have been received from errc

	go func() {
		err := p2p.Send(rw, NewSignerMsg, &SignerStatusData{
			ProtocolVersion: uint32(ProtocolVersion),
			Mac:             mac,
			Sig:             sig,
		})
		errc <- err
	}()
	go func() {
		address, err = ReadValidatorStatus(p, rw, &signerStatus, term, futureTerm)
		errc <- err
	}()
	timeout := time.NewTimer(handshakeTimeout)
	defer timeout.Stop()
	for i := 0; i < 2; i++ {
		select {
		case err := <-errc:
			if err != nil {
				log.Debug("err when handshaking", "err", err)
				return common.Address{}, err
			}
		case <-timeout.C:
			log.Debug("handshaking time out", "err", err)
			return common.Address{}, p2p.DiscReadTimeout
		}
	}
	return address, nil
}

// ReadValidatorStatus reads status of remote validator
func ReadValidatorStatus(p *p2p.Peer, rw p2p.MsgReadWriter, signerStatusData *SignerStatusData, term uint64, futureTerm uint64) (address common.Address, err error) {
	msg, err := rw.ReadMsg()
	if err != nil {
		return common.Address{}, err
	}
	if msg.Code != NewSignerMsg {
		return common.Address{}, errResp(ErrNoStatusMsg, "first msg has code %x (!= %x)", msg.Code, NewSignerMsg)
	}
	if msg.Size > ProtocolMaxMsgSize {
		return common.Address{}, errResp(ErrMsgTooLarge, "%v > %v", msg.Size, ProtocolMaxMsgSize)
	}
	// Decode the handshake and make sure everything matches
	if err := msg.Decode(&signerStatusData); err != nil {
		return common.Address{}, errResp(ErrDecode, "msg %v: %v", msg, err)
	}
	if int(signerStatusData.ProtocolVersion) != ProtocolVersion {
		return common.Address{}, errResp(ErrProtocolVersionMismatch, "%d (!= %d)", signerStatusData.ProtocolVersion, ProtocolVersion)
	}

	mac, sig := signerStatusData.Mac, signerStatusData.Sig
	valid, address, err := ValidMacSig(mac, sig)
	if valid {
		return
	}

	address = common.Address{}
	return
}

// fetchNodeID fetches node id of proposer encrypted with validator's public key
func fetchNodeID(term uint64, proposer common.Address, validator common.Address, contractInstance *contracts.ProposerRegister) ([]byte, error) {
	callOpts := &bind.CallOpts{
		From: validator,
	}
	encryptedNodeID, err := contractInstance.GetNodeInfo(callOpts, big.NewInt(int64(term)), proposer)
	if err != nil {
		return nil, err
	}
	return encryptedNodeID, nil
}
