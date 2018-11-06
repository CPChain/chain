package backend

import (
	"context"
	"encoding/hex"
	"math/big"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/signerRegister"
	"bitbucket.org/cpchain/chain/types"
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

// Signer represents a remote signer waiting to be connected and communicate with.
type Signer struct {
	*p2p.Peer
	rw      p2p.MsgReadWriter
	version int

	epochIdx      uint64
	pubkey        []byte
	nodeID        string
	address       common.Address
	dialed        bool // bool to show if i already connected to this signer.
	pubkeyFetched bool
	nodeIDFetched bool
	nodeIDUpdated bool // bool to show if i updated my nodeid encrypted with this signer's pubkey to the contract.

	queuedPendingBlocks chan *types.Block  // Queue of blocks to broadcast to the signer
	queuedPrepareSigs   chan *types.Header // Queue of signatures to broadcast to the signer
	queuedCommitSigs    chan *types.Header // Queue of signatures to broadcast to the signer

	term chan struct{} // Termination channel to stop the broadcaster

	lock sync.RWMutex
}

// SetSigner sets a signer
func (rs *Signer) SetSigner(version int, p *p2p.Peer, rw p2p.MsgReadWriter) error {
	rs.lock.Lock()
	defer rs.lock.Unlock()

	rs.version, rs.Peer, rs.rw = version, p, rw

	return nil
}

// NewSigner creates a new NewSigner with given view idx and address.
func NewSigner(epochIdx uint64, address common.Address) *Signer {
	return &Signer{
		epochIdx: epochIdx,
		address:  address,

		queuedPendingBlocks: make(chan *types.Block, maxQueuedPendingBlocks),
		queuedPrepareSigs:   make(chan *types.Header, maxQueuedSigs),
		queuedCommitSigs:    make(chan *types.Header, maxQueuedSigs),

		term: make(chan struct{}),
	}
}

// fetchPubkey fetches the public key of the remote signer from the contract.
func (rs *Signer) fetchPubkey(contractInstance *contract.SignerConnectionRegister) error {

	address := rs.address

	log.Debug("fetching public key of remote signer")
	log.Debug("signer", "addr", address)

	pubkey, err := contractInstance.GetPublicKey(nil, address)
	if err != nil {
		return err
	}

	rs.pubkey = pubkey
	rs.pubkeyFetched = true

	log.Debug("fetched public key of remote signer", "pubkey", pubkey)

	return nil
}

// fetchNodeID fetches the node id of the remote signer encrypted with my public key, and decrypts it with my private key.
func (rs *Signer) fetchNodeID(contractInstance *contract.SignerConnectionRegister, rsaKey *rsakey.RsaKey) error {
	epochIdx, address := rs.epochIdx, rs.address

	log.Debug("fetching nodeID of remote signer")
	log.Debug("epoch", "idx", epochIdx)
	log.Debug("signer", "addr", address.Hex())

	encryptedNodeID, err := fetchNodeID(epochIdx, address, contractInstance)
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
	rs.nodeID = nodeID
	rs.nodeIDFetched = true

	log.Debug("fetched nodeID of remote signer", "nodeID", nodeID)

	return nil
}

func fetchNodeID(epochIdx uint64, address common.Address, contractInstance *contract.SignerConnectionRegister) ([]byte, error) {
	encryptedNodeID, err := contractInstance.GetNodeInfo(nil, big.NewInt(int64(epochIdx)), address)
	if err != nil {
		return nil, err
	}
	return encryptedNodeID, nil
}

// updateNodeID encrypts my node id with this remote signer's public key and update to the contract.
func (rs *Signer) updateNodeID(nodeID string, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client ClientBackend) error {
	epochIdx, address := rs.epochIdx, rs.address

	log.Debug("fetched rsa pubkey")
	log.Debug(hex.Dump(rs.pubkey))

	pubkey, err := rsakey.NewRsaPublicKey(rs.pubkey)

	log.Debug("updating self nodeID with remote signer's public key")
	log.Debug("epoch", "idx", epochIdx)
	log.Debug("signer", "addr", address.Hex())
	log.Debug("nodeID", "nodeID", nodeID)
	log.Debug("pubkey", "pubkey", pubkey)

	if err != nil {
		return err
	}

	encryptedNodeID, err := pubkey.RsaEncrypt([]byte(nodeID))

	log.Debug("encryptedNodeID")
	log.Debug(hex.Dump(encryptedNodeID))

	transaction, err := contractInstance.AddNodeInfo(auth, big.NewInt(int64(epochIdx)), address, encryptedNodeID)
	if err != nil {
		return err
	}

	ctx := context.Background()
	_, err = bind.WaitMined(ctx, client, transaction)
	if err != nil {
		return err
	}

	rs.nodeIDUpdated = true

	log.Debug("updated self nodeID")

	return nil
}

// dial dials the signer.
func (rs *Signer) dial(server *p2p.Server, nodeID string, address common.Address, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client ClientBackend, rsaKey *rsakey.RsaKey) (bool, error) {
	rs.lock.Lock()
	defer rs.lock.Unlock()

	log.Debug("dialing to remote signer", "signer", rs)

	// fetch remtoe signer's public key if there is no one.
	if !rs.pubkeyFetched {
		err := rs.fetchPubkey(contractInstance)
		if err != nil {
			log.Warn("err when fetching signer's pubkey from contract", "err", err)
			return false, err
		}
	}

	nodeid, err := fetchNodeID(rs.epochIdx, address, contractInstance)
	if err != nil {
		return false, err
	}

	// update my nodeID to contract if already know the public key of the remote signer and not updated yet.
	if rs.pubkeyFetched && len(nodeid) == 0 {
		err := rs.updateNodeID(nodeID, auth, contractInstance, client)
		if err != nil {
			log.Warn("err when updating my node id to contract", "err", err)
			return false, err
		}
	}

	// fetch the nodeID of the remote signer if not fetched yet.
	if !rs.nodeIDFetched {
		err := rs.fetchNodeID(contractInstance, rsaKey)
		if err != nil {
			log.Warn("err when fetching signer's nodeID from contract", "err", err)
			return false, err
		}
	}

	// dial the signer with his nodeID if not dialed yet.
	if rs.nodeIDFetched && !rs.dialed {
		node, err := discover.ParseNode(rs.nodeID)
		if err != nil {
			log.Warn("err when dialing remote signer with his nodeID", "err", err)
			return false, err
		}
		if server != nil {
			server.AddPeer(node)
		} else {
			log.Warn("invalid server", "server", server)
		}
		rs.dialed = true
	}

	return rs.dialed, nil
}

// Dial dials the signer
func (rs *Signer) Dial(server *p2p.Server, nodeID string, address common.Address, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client ClientBackend, rsaKey *rsakey.RsaKey) error {

	succeed, err := rs.dial(server, nodeID, address, auth, contractInstance, client, rsaKey)
	// succeed, err := func() (bool, error) { return true, nil }()

	log.Debug("result of rs.dial", "succeed", succeed)
	log.Debug("result of rs.dial", "err", err)

	if succeed || err == nil {
		return nil
	}
	return nil
}

func (rs *Signer) disconnect(server *p2p.Server) error {
	rs.lock.Lock()
	nodeID := rs.nodeID
	rs.lock.Unlock()

	node, err := discover.ParseNode(nodeID)
	if err != nil {
		return err
	}
	server.RemovePeer(node)
	return nil
}

// signerBroadcast is a write loop that multiplexes block propagations, announcements
// and transaction broadcasts into the remote peer. The goal is to have an async
// writer that does not lock up node internals.
func (p *Signer) signerBroadcast() {
	for {
		select {
		// blocks waiting for signatures
		case block := <-p.queuedPendingBlocks:
			if err := p.SendNewPendingBlock(block); err != nil {
				return
			}
			p.Log().Trace("Propagated generated block", "number", block.Number(), "hash", block.Hash())

		case header := <-p.queuedPrepareSigs:
			if err := p.SendPrepareSignedHeader(header); err != nil {
				return
			}
			p.Log().Trace("Propagated signed prepare header", "number", header.Number, "hash", header.Hash())

		case header := <-p.queuedCommitSigs:
			if err := p.SendCommitSignedHeader(header); err != nil {
				return
			}
			p.Log().Trace("Propagated signed commit header", "number", header.Number, "hash", header.Hash())

		case <-p.term:
			return
		}
	}
}

func (p *Signer) SendNewSignerMsg(eb common.Address) error {
	return p2p.Send(p.rw, NewSignerMsg, eb)
}

// SendNewPendingBlock propagates an entire block to a remote peer.
func (p *Signer) SendNewPendingBlock(block *types.Block) error {
	return p2p.Send(p.rw, PrepreparePendingBlockMsg, block)
}

// AsyncSendNewPendingBlock queues an entire block for propagation to a remote peer. If
// the peer's broadcast queue is full, the event is silently dropped.
func (p *Signer) AsyncSendNewPendingBlock(block *types.Block) {
	select {
	case p.queuedPendingBlocks <- block:
	default:
		p.Log().Debug("Dropping block propagation", "number", block.NumberU64(), "hash", block.Hash())
	}
}

// SendPrepareSignedHeader sends new signed block header.
func (p *Signer) SendPrepareSignedHeader(header *types.Header) error {
	err := p2p.Send(p.rw, PrepareSignedHeaderMsg, header)
	return err
}

func (p *Signer) AsyncSendPrepareSignedHeader(header *types.Header) {
	select {
	case p.queuedPrepareSigs <- header:
	default:
		p.Log().Debug("Dropping signature propagation", "number", header.Number, "hash", header.Hash())
	}
}

// SendCommitSignedHeader sends new signed block header.
func (p *Signer) SendCommitSignedHeader(header *types.Header) error {
	err := p2p.Send(p.rw, CommitSignedHeaderMsg, header)
	return err
}

func (p *Signer) AsyncSendCommitSignedHeader(header *types.Header) {
	select {
	case p.queuedCommitSigs <- header:
	default:
		p.Log().Debug("Dropping signature propagation", "number", header.Number, "hash", header.Hash())
	}
}

func Handshake(p *p2p.Peer, rw p2p.MsgReadWriter, etherbase common.Address, signerValidator ValidateSignerFn) (isSigner bool, address common.Address, err error) {
	// Send out own handshake in a new thread
	errc := make(chan error, 2)
	var signerStatus signerStatusData // safe to read after two values have been received from errc

	log.Debug("my etherbase", "address", etherbase)

	go func() {
		errc <- p2p.Send(rw, NewSignerMsg, &signerStatusData{
			ProtocolVersion: uint32(ProtocolVersion),
			Address:         etherbase,
		})
	}()
	go func() {
		isSigner, address, err = ReadSignerStatus(p, rw, &signerStatus, signerValidator)
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
	return isSigner, address, nil
}

func ReadSignerStatus(p *p2p.Peer, rw p2p.MsgReadWriter, signerStatus *signerStatusData, signerValidator ValidateSignerFn) (isSigner bool, address common.Address, err error) {
	msg, err := rw.ReadMsg()
	if err != nil {
		return false, common.Address{}, err
	}
	if msg.Code != NewSignerMsg {
		return false, common.Address{}, errResp(ErrNoStatusMsg, "first msg has code %x (!= %x)", msg.Code, NewSignerMsg)
	}
	if msg.Size > ProtocolMaxMsgSize {
		return false, common.Address{}, errResp(ErrMsgTooLarge, "%v > %v", msg.Size, ProtocolMaxMsgSize)
	}
	// Decode the handshake and make sure everything matches
	if err := msg.Decode(&signerStatus); err != nil {
		return false, common.Address{}, errResp(ErrDecode, "msg %v: %v", msg, err)
	}
	if int(signerStatus.ProtocolVersion) != ProtocolVersion {
		return false, common.Address{}, errResp(ErrProtocolVersionMismatch, "%d (!= %d)", signerStatus.ProtocolVersion, ProtocolVersion)
	}

	// TODO: this (addr, ...) pair should be signed with its private key.
	// @liuq

	isSigner, err = signerValidator(signerStatus.Address)
	log.Debug("cpchain committee network handshaking...")
	log.Debug("peer is signer", "peer", signerStatus.Address, isSigner)
	return isSigner, signerStatus.Address, err
}
