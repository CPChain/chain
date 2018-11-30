package backend

import (
	"context"
	"encoding/hex"
	"fmt"
	"math/big"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/proposer_register"
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
	pubkey  []byte
	nodeID  string
	address common.Address

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
func NewRemoteSigner(term uint64, address common.Address) *RemoteSigner {
	return &RemoteSigner{
		term:    term,
		address: address,
	}

}

// NewRemoteProposer creates a new remote proposer
func NewRemoteProposer(term uint64, address common.Address) *RemoteProposer {
	return &RemoteProposer{
		RemoteSigner: NewRemoteSigner(term, address),
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

// fetchPubkey fetches the public key of the remote signer from the contract.
func (s *RemoteSigner) fetchPubkey(contractInstance *contract.ProposerRegister) error {

	address := s.address

	log.Debug("fetching public key of remote signer")
	log.Debug("signer", "addr", address)

	pubkey, err := contractInstance.GetPublicKey(nil, address)
	if err != nil {
		return err
	}

	s.pubkey = pubkey
	s.pubkeyFetched = true

	log.Debug("fetched public key of remote signer", "pubkey", pubkey)

	return nil
}

// fetchNodeID fetches the node id of the remote signer encrypted with my public key, and decrypts it with my private key.
func (s *RemoteSigner) fetchNodeID(contractInstance *contract.ProposerRegister, rsaKey *rsakey.RsaKey) error {
	term, address := s.term, s.address

	log.Debug("fetching nodeID of remote signer")
	log.Debug("epoch", "idx", term)
	log.Debug("signer", "addr", address.Hex())

	encryptedNodeID, err := fetchNodeID(term, address, contractInstance)
	nodeid, err := rsaKey.RsaDecrypt(encryptedNodeID)
	if err != nil {
		log.Debug("encryptedNodeID")
		log.Debug(hex.Dump(encryptedNodeID))
		log.Debug("my pubkey")
		log.Debug(hex.Dump(rsaKey.PublicKey.RsaPublicKeyBytes))
		log.Debug("privKey", "privKey", rsaKey.PrivateKey)
		return err
	}

	nodeID := string(nodeid)
	s.nodeID = nodeID
	s.nodeIDFetched = true

	log.Debug("fetched nodeID of remote signer", "nodeID", nodeID)

	return nil
}

func fetchNodeID(term uint64, address common.Address, contractInstance *contract.ProposerRegister) ([]byte, error) {
	encryptedNodeID, err := contractInstance.GetNodeInfo(nil, big.NewInt(int64(term)), address)
	if err != nil {
		return nil, err
	}
	return encryptedNodeID, nil
}

// uploadNodeID encrypts my node id with this remote signer's public key and update to the contract.
func (s *RemoteSigner) uploadNodeID(nodeID string, auth *bind.TransactOpts, contractInstance *contract.ProposerRegister, client ClientBackend) error {
	term, address := s.term, s.address

	log.Debug("fetched rsa pubkey")
	log.Debug(hex.Dump(s.pubkey))

	pubkey, err := rsakey.NewRsaPublicKey(s.pubkey)

	log.Debug("updating self nodeID with remote signer's public key")
	log.Debug("epoch", "idx", term)
	log.Debug("signer", "addr", address.Hex())
	log.Debug("nodeID", "nodeID", nodeID)
	log.Debug("pubkey", "pubkey", pubkey)

	if err != nil {
		return err
	}

	encryptedNodeID, err := pubkey.RsaEncrypt([]byte(nodeID))

	log.Debug("encryptedNodeID")
	log.Debug(hex.Dump(encryptedNodeID))

	transaction, err := contractInstance.AddNodeInfo(auth, big.NewInt(int64(term)), address, encryptedNodeID)
	if err != nil {
		return err
	}

	ctx := context.Background()
	_, err = bind.WaitMined(ctx, client, transaction)
	if err != nil {
		return err
	}

	s.nodeIDUpdated = true

	log.Debug("updated self nodeID")

	return nil
}

// uploadNodeInfo upload my nodeID the signer.
func (s *RemoteSigner) uploadNodeInfo(
	nodeID string,
	address common.Address,
	auth *bind.TransactOpts,
	contractInstance *contract.ProposerRegister,
	client ClientBackend,
) (bool, error) {

	s.lock.Lock()
	defer s.lock.Unlock()

	log.Debug("dialing to remote signer", "signer", s)

	// fetch remote signer's public key if there is no one.
	if !s.pubkeyFetched {
		err := s.fetchPubkey(contractInstance)
		if err != nil {
			log.Warn("err when fetching signer's pubkey from contract", "err", err)
			return false, err
		}
	}

	nodeid, err := fetchNodeID(s.term, address, contractInstance)
	if err != nil {
		return false, err
	}

	// update my nodeID to contract if already know the public key of the remote signer and not updated yet.
	if s.pubkeyFetched && len(nodeid) == 0 {
		err := s.uploadNodeID(nodeID, auth, contractInstance, client)
		if err != nil {
			log.Warn("err when updating my node id to contract", "err", err)
			return false, err
		}
	}

	return true, nil
}

func (s *RemoteSigner) fetchNodeInfoAndDial(
	server *p2p.Server,
	rsaKey *rsakey.RsaKey,
	contractInstance *contract.ProposerRegister,
) (bool, error) {

	// fetch the nodeID of the remote signer if not fetched yet.
	if !s.nodeIDFetched {
		err := s.fetchNodeID(contractInstance, rsaKey)
		if err != nil {
			log.Warn("err when fetching signer's nodeID from contract", "err", err)
			return false, err
		}
	}

	// dial the signer with his nodeID if not dialed yet.
	if s.nodeIDFetched && !s.dialed {
		node, err := discover.ParseNode(s.nodeID)
		if err != nil {
			log.Warn("err when dialing remote signer with his nodeID", "err", err)
			return false, err
		}
		if server != nil {
			server.AddPeer(node)
		} else {
			log.Warn("invalid server", "server", server)
		}
		s.dialed = true
	}

	return s.dialed, nil
}

// Dial dials the signer
func (s *RemoteSigner) Dial(server *p2p.Server, nodeID string, address common.Address, auth *bind.TransactOpts, contractInstance *contract.ProposerRegister, client ClientBackend, rsaKey *rsakey.RsaKey) (bool, error) {

	succeed, err := s.uploadNodeInfo(nodeID, address, auth, contractInstance, client)
	if !succeed || err != nil {
		return false, err
	}

	succeed, err = s.fetchNodeInfoAndDial(server, rsaKey, contractInstance)
	if !succeed || err != nil {
		return false, err
	}

	log.Debug("result of rs.dial", "succeed", succeed)
	log.Debug("result of rs.dial", "err", err)

	return true, nil
}
