package backend

import (
	"context"
	"encoding/hex"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/signerRegister"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
)

// Signer represents a remote signer waiting to be connected and communicate with.
type Signer struct {
	epochIdx      uint64
	pubkey        []byte
	nodeID        string
	address       common.Address
	pubkeyFetched bool
	nodeIDFetched bool
	nodeIDUpdated bool // bool to show if i updated my nodeid encrypted with this signer's pubkey to the contract.
	dialed        bool // bool to show if i already connected to this signer.

	lock sync.RWMutex
}

// NewSigner creates a new NewSigner with given view idx and address.
func NewSigner(epochIdx uint64, address common.Address) *Signer {
	return &Signer{
		epochIdx: epochIdx,
		address:  address,
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
func (rs *Signer) updateNodeID(nodeID string, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client consensus.ClientBackend) error {
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
func (rs *Signer) dial(server *p2p.Server, nodeID string, address common.Address, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client consensus.ClientBackend, rsaKey *rsakey.RsaKey) (bool, error) {
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

func (rs *Signer) Dial(server *p2p.Server, nodeID string, address common.Address, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client consensus.ClientBackend, rsaKey *rsakey.RsaKey) error {

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

// BasicCommitteeHandler implements consensus.CommitteeHandler
type BasicCommitteeHandler struct {
	epochIdx uint64

	ownNodeID  string
	ownAddress common.Address

	server *p2p.Server

	contractAddress    common.Address
	contractCaller     *consensus.ContractCaller
	contractInstance   *contract.SignerConnectionRegister
	contractTransactor *bind.TransactOpts

	RsaKey *rsakey.RsaKey

	remoteSigners []*Signer

	connected bool
	lock      sync.RWMutex
}

// NewBasicCommitteeNetworkHandler creates a BasicCommitteeNetworkHandler instance
func NewBasicCommitteeNetworkHandler(config *configs.DporConfig, etherbase common.Address) (*BasicCommitteeHandler, error) {
	ch := &BasicCommitteeHandler{
		ownAddress:      etherbase,
		contractAddress: config.Contracts["signer"],
		remoteSigners:   make([]*Signer, config.Epoch),
		// remoteSigners:   make([]*Signer, config.Epoch-1),
		connected: false,
	}
	return ch, nil
}

func (ch *BasicCommitteeHandler) UpdateServer(server *p2p.Server) error {
	ch.lock.Lock()
	defer ch.lock.Unlock()
	ch.server = server
	ch.ownNodeID = server.Self().String()
	return nil
}

func (ch *BasicCommitteeHandler) SetRSAKeys(rsaReader RSAReader) error {
	ch.lock.Lock()
	defer ch.lock.Unlock()

	var err error

	ch.RsaKey, err = rsaReader()

	return err
}

// UpdateContractCaller updates contractcaller.
func (ch *BasicCommitteeHandler) UpdateContractCaller(contractCaller *consensus.ContractCaller) error {

	// creates an contract instance
	contractInstance, err := contract.NewSignerConnectionRegister(ch.contractAddress, contractCaller.Client)
	if err != nil {
		return err
	}

	// creates a keyed transactor
	auth := bind.NewKeyedTransactor(contractCaller.Key.PrivateKey)

	gasPrice, err := contractCaller.Client.SuggestGasPrice(context.Background())
	if err != nil {
		return err
	}

	auth.Value = big.NewInt(0)
	auth.GasLimit = contractCaller.GasLimit
	auth.GasPrice = gasPrice

	ch.lock.Lock()

	// assign
	ch.contractCaller = contractCaller
	ch.contractInstance = contractInstance
	ch.contractTransactor = auth

	ch.lock.Unlock()

	return nil
}

// UpdateSigners updates BasicCommitteeNetworkHandler's remoteSigners.
func (ch *BasicCommitteeHandler) UpdateSigners(epochIdx uint64, signers []common.Address) error {
	ch.lock.Lock()
	remoteSigners := ch.remoteSigners
	ch.lock.Unlock()

	log.Debug("remote signers", "signers", signers)
	log.Debug("ch.remoteSigners", "signers", remoteSigners)

	for i, signer := range signers {
		// if remoteSigners[i] == nil || remoteSigners[i].address != signer {
		if remoteSigners[i] == nil {

			// // omit self
			// if signer == ch.contractTransactor.From {
			// 	continue
			// }
			s := NewSigner(epochIdx, signer)
			remoteSigners[i] = s
		}
	}

	ch.lock.Lock()
	ch.epochIdx = epochIdx
	ch.remoteSigners = remoteSigners
	ch.lock.Unlock()

	return nil
}

// DialAll connects remote signers.
func (ch *BasicCommitteeHandler) DialAll() {
	ch.lock.Lock()
	nodeID, address, contractInstance, auth, client := ch.ownNodeID, ch.ownAddress, ch.contractInstance, ch.contractTransactor, ch.contractCaller.Client
	connected, remoteSigners, server := ch.connected, ch.remoteSigners, ch.server
	rsaKey := ch.RsaKey
	ch.lock.Unlock()

	if !connected {
		log.Debug("connecting...")

		for _, s := range remoteSigners {
			err := s.Dial(server, nodeID, address, auth, contractInstance, client, rsaKey)
			log.Debug("err when connect", "e", err)
		}
		connected = true
	}

	ch.lock.Lock()
	ch.connected = connected
	ch.lock.Unlock()

}

// Disconnect disconnects all.
func (ch *BasicCommitteeHandler) Disconnect() {
	ch.lock.Lock()
	connected, remoteSigners, server := ch.connected, ch.remoteSigners, ch.server
	ch.lock.Unlock()

	if connected {
		log.Debug("disconnecting...")

		for _, s := range remoteSigners {
			err := s.disconnect(server)
			log.Debug("err when disconnect", "e", err)
		}

		ch.connected = false
	}

	ch.lock.Lock()
	ch.connected = connected
	ch.lock.Unlock()
}
