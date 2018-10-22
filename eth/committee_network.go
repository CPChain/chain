package eth

import (
	"context"
	"encoding/hex"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/contracts/dpor/contract/signerRegister"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
)

// RemoteSigner represents a remote signer waiting to be connected and communicate with.
type RemoteSigner struct {
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

// NewRemoteSigner creates a new NewRemoteSigner with given view idx and address.
func NewRemoteSigner(epochIdx uint64, address common.Address) *RemoteSigner {
	return &RemoteSigner{
		epochIdx: epochIdx,
		address:  address,
	}
}

// fetchPubkey fetches the public key of the remote signer from the contract.
func (rs *RemoteSigner) fetchPubkey(contractInstance *contract.SignerConnectionRegister) error {

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
func (rs *RemoteSigner) fetchNodeID(contractInstance *contract.SignerConnectionRegister, rsaKey *rsakey.RsaKey) error {
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
func (rs *RemoteSigner) updateNodeID(nodeID string, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client dpor.ClientBackend) error {
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
func (rs *RemoteSigner) dial(server *p2p.Server, nodeID string, address common.Address, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client dpor.ClientBackend, rsaKey *rsakey.RsaKey) (bool, error) {
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
		server.AddPeer(node)
		rs.dialed = true
	}

	return rs.dialed, nil
}

func (rs *RemoteSigner) Dial(server *p2p.Server, nodeID string, address common.Address, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client dpor.ClientBackend, rsaKey *rsakey.RsaKey) error {

	succeed, err := rs.dial(server, nodeID, address, auth, contractInstance, client, rsaKey)
	// succeed, err := func() (bool, error) { return true, nil }()

	log.Debug("result of rs.dial", "succeed", succeed)
	log.Debug("result of rs.dial", "err", err)

	if succeed || err == nil {
		return nil
	}
	return nil
}

func (rs *RemoteSigner) disconnect(server *p2p.Server) error {
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

// BasicCommitteeNetworkHandler implements consensus.CommitteeNetworkHandler
type BasicCommitteeNetworkHandler struct {
	epochIdx uint64

	ownNodeID  string
	ownAddress common.Address

	server *p2p.Server

	contractAddress    common.Address
	contractCaller     *dpor.ContractCaller
	contractInstance   *contract.SignerConnectionRegister
	contractTransactor *bind.TransactOpts

	RsaKey *rsakey.RsaKey

	remoteSigners []*RemoteSigner

	connected bool
	lock      sync.RWMutex
}

// NewBasicCommitteeNetworkHandler creates a BasicCommitteeNetworkHandler instance
func NewBasicCommitteeNetworkHandler(config *configs.DporConfig, etherbase common.Address) (*BasicCommitteeNetworkHandler, error) {
	bc := &BasicCommitteeNetworkHandler{
		ownAddress:      etherbase,
		contractAddress: config.Contracts["signer"],
		remoteSigners:   make([]*RemoteSigner, config.Epoch),
		// remoteSigners:   make([]*RemoteSigner, config.Epoch-1),
		connected: false,
	}
	return bc, nil
}

func (oc *BasicCommitteeNetworkHandler) UpdateServer(server *p2p.Server) error {
	oc.lock.Lock()
	defer oc.lock.Unlock()
	oc.server = server
	oc.ownNodeID = server.Self().String()
	return nil
}

func (oc *BasicCommitteeNetworkHandler) SetRSAKeys(rsaReader RSAReader) error {
	oc.lock.Lock()
	defer oc.lock.Unlock()

	var err error

	oc.RsaKey, err = rsaReader()

	return err
}

// UpdateContractCaller updates contractcaller.
func (oc *BasicCommitteeNetworkHandler) UpdateContractCaller(contractCaller *dpor.ContractCaller) error {

	// creates an contract instance
	contractInstance, err := contract.NewSignerConnectionRegister(oc.contractAddress, contractCaller.Client)
	if err != nil {
		return err
	}

	// creates a keyed transactor
	auth := bind.NewKeyedTransactor(contractCaller.Key.PrivateKey)

	auth.Value = big.NewInt(0)
	auth.GasLimit = contractCaller.GasLimit
	auth.GasPrice = big.NewInt(int64(contractCaller.GasPrice))

	oc.lock.Lock()

	// assign
	oc.contractCaller = contractCaller
	oc.contractInstance = contractInstance
	oc.contractTransactor = auth

	oc.lock.Unlock()

	return nil
}

// UpdateRemoteSigners updates BasicCommitteeNetworkHandler's remoteSigners.
func (oc *BasicCommitteeNetworkHandler) UpdateRemoteSigners(epochIdx uint64, signers []common.Address) error {
	oc.lock.Lock()
	remoteSigners := oc.remoteSigners
	oc.lock.Unlock()

	log.Debug("remote signers", "signers", signers)
	log.Debug("oc.remoteSigners", "signers", remoteSigners)

	for i, signer := range signers {
		// if remoteSigners[i] == nil || remoteSigners[i].address != signer {
		if remoteSigners[i] == nil {

			// // omit self
			// if signer == oc.contractTransactor.From {
			// 	continue
			// }
			s := NewRemoteSigner(epochIdx, signer)
			remoteSigners[i] = s
		}
	}

	oc.lock.Lock()
	oc.epochIdx = epochIdx
	oc.remoteSigners = remoteSigners
	oc.lock.Unlock()

	return nil
}

// Connect connects remote signers.
func (oc *BasicCommitteeNetworkHandler) Connect() {
	oc.lock.Lock()
	nodeID, address, contractInstance, auth, client := oc.ownNodeID, oc.ownAddress, oc.contractInstance, oc.contractTransactor, oc.contractCaller.Client
	connected, remoteSigners, server := oc.connected, oc.remoteSigners, oc.server
	rsaKey := oc.RsaKey
	oc.lock.Unlock()

	if !connected {
		log.Debug("connecting...")

		for _, s := range remoteSigners {
			err := s.Dial(server, nodeID, address, auth, contractInstance, client, rsaKey)
			log.Debug("err when connect", "e", err)
		}
		connected = true
	}

	oc.lock.Lock()
	oc.connected = connected
	oc.lock.Unlock()

}

// Disconnect disconnects all.
func (oc *BasicCommitteeNetworkHandler) Disconnect() {
	oc.lock.Lock()
	connected, remoteSigners, server := oc.connected, oc.remoteSigners, oc.server
	oc.lock.Unlock()

	if connected {
		log.Debug("disconnecting...")

		for _, s := range remoteSigners {
			err := s.disconnect(server)
			log.Debug("err when disconnect", "e", err)
		}

		oc.connected = false
	}

	oc.lock.Lock()
	oc.connected = connected
	oc.lock.Unlock()
}
