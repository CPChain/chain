package eth

import (
	"context"
	"crypto/rsa"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/rsa_"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/contracts/dpor/contract/signerRegister"
	"bitbucket.org/cpchain/chain/p2p"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/log"
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

	log.Info("fetching public key of remote signer")
	log.Info("signer", "addr", address)

	pubkey, err := contractInstance.GetPublicKey(nil, address)
	if err != nil {
		return err
	}

	rs.pubkey = pubkey
	rs.pubkeyFetched = true

	log.Info("fetched public key of remote signer", "pubkey", pubkey)

	return nil
}

// fetchNodeID fetches the node id of the remote signer encrypted with my public key, and decrypts it with my private key.
func (rs *RemoteSigner) fetchNodeID(contractInstance *contract.SignerConnectionRegister, privKey *rsa.PrivateKey) error {
	epochIdx, address := rs.epochIdx, rs.address

	log.Info("fetching nodeID of remote signer")
	log.Info("epoch", "idx", epochIdx)
	log.Info("signer", "addr", address)

	encryptedNodeID, err := fetchNodeID(epochIdx, address, contractInstance, privKey)
	nodeid, err := rsa_.RsaDecrypt(encryptedNodeID, privKey)
	if err != nil {
		log.Info("encryptedNodeID", "enode", encryptedNodeID)
		log.Info("privKey", "privKey", privKey)
		return err
	}

	nodeID := string(nodeid)
	rs.nodeID = nodeID
	rs.nodeIDFetched = true

	log.Info("fetched nodeID of remote signer", "nodeID", nodeID)

	return nil
}

func fetchNodeID(epochIdx uint64, address common.Address, contractInstance *contract.SignerConnectionRegister, privKey *rsa.PrivateKey) ([]byte, error) {
	encryptedNodeID, err := contractInstance.GetNodeInfo(nil, big.NewInt(int64(epochIdx)), address)
	if err != nil {
		return nil, err
	}
	return encryptedNodeID, nil
}

// updateNodeID encrypts my node id with this remote signer's public key and update to the contract.
func (rs *RemoteSigner) updateNodeID(nodeID string, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client dpor.ClientBackend) error {
	epochIdx, address := rs.epochIdx, rs.address
	pubkey, err := rsa_.Bytes2PublicKey(rs.pubkey)

	log.Info("updating self nodeID with remote signer's public key")
	log.Info("epoch", "idx", epochIdx)
	log.Info("signer", "addr", address)
	log.Info("nodeID", "nodeID", nodeID)
	log.Info("pubkey", "pubkey", pubkey)

	if err != nil {
		return err
	}

	encryptedNodeID, err := rsa_.RsaEncrypt([]byte(nodeID), pubkey)
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

	log.Info("updated self nodeID")

	return nil
}

// dial dials the signer.
func (rs *RemoteSigner) dial(server *p2p.Server, nodeID string, address common.Address, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client dpor.ClientBackend) (bool, error) {
	rs.lock.Lock()
	defer rs.lock.Unlock()

	log.Info("dialing to remote signer", "signer", rs)

	// fetch remtoe signer's public key if there is no one.
	if !rs.pubkeyFetched {
		err := rs.fetchPubkey(contractInstance)
		if err != nil {
			log.Warn("err when fetching signer's pubkey from contract", "err", err)
			return false, err
		}
	}

	nodeid, err := fetchNodeID(rs.epochIdx, address, contractInstance, server.RsaPrivateKey)
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
		err := rs.fetchNodeID(contractInstance, server.RsaPrivateKey)
		if err != nil {
			log.Warn("err when fetching signer's nodeID from contract", "err", err)
			return false, err
		}
	}

	// dial the signer with his nodeID if not dialed yet.
	if rs.nodeIDFetched && !rs.dialed {
		err := server.AddPeerFromURL(rs.nodeID)
		if err != nil {
			log.Warn("err when dialing remote signer with his nodeID", "err", err)
			return false, err
		}
	}

	return rs.dialed, nil
}

func (rs *RemoteSigner) Dial(server *p2p.Server, nodeID string, address common.Address, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client dpor.ClientBackend) error {

	succeed, err := rs.dial(server, nodeID, address, auth, contractInstance, client)

	log.Info("result of rs.dial", "succeed", succeed)
	log.Info("result of rs.dial", "err", err)

	if succeed || err == nil {
		return nil
	}
	return nil
}

func (rs *RemoteSigner) disconnect(server *p2p.Server) error {
	rs.lock.Lock()
	nodeID := rs.nodeID
	rs.lock.Unlock()

	err := server.RemovePeerFromURL(nodeID)
	return err
}

// BasicCommitteeNetworkHandler implements consensus.CommitteeNetworkHandler
type BasicCommitteeNetworkHandler struct {
	epochIdx uint64

	ownNodeID  string
	ownPubkey  []byte
	ownAddress common.Address

	server *p2p.Server

	contractAddress    common.Address
	contractCaller     *dpor.ContractCaller
	contractInstance   *contract.SignerConnectionRegister
	contractTransactor *bind.TransactOpts

	remoteSigners []*RemoteSigner

	connected bool
	lock      sync.RWMutex
}

// NewBasicCommitteeNetworkHandler creates a BasicCommitteeNetworkHandler instance
func NewBasicCommitteeNetworkHandler(epochLength uint64, ownAddress common.Address, contractAddress common.Address, server *p2p.Server) (*BasicCommitteeNetworkHandler, error) {
	bc := &BasicCommitteeNetworkHandler{
		server:          server,
		ownNodeID:       server.Self().String(),
		ownPubkey:       server.RsaPublicKeyBytes,
		ownAddress:      ownAddress,
		contractAddress: contractAddress,
		remoteSigners:   make([]*RemoteSigner, epochLength-1),
		connected:       false,
	}
	return bc, nil
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

	log.Info("remote signers", "signers", signers)
	log.Info("oc.remoteSigners", "signers", remoteSigners)

	for i, signer := range signers {
		// if remoteSigners[i] == nil || remoteSigners[i].address != signer {
		if remoteSigners[i] == nil {

			// omit self
			if signer == oc.contractTransactor.From {
				continue
			}
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
	oc.lock.Unlock()

	if !connected {
		log.Info("connecting...")

		for _, s := range remoteSigners {
			err := s.Dial(server, nodeID, address, auth, contractInstance, client)
			log.Info("err when connect", "e", err)
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
		log.Info("disconnecting...")

		for _, s := range remoteSigners {
			err := s.disconnect(server)
			log.Info("err when disconnect", "e", err)
		}

		oc.connected = false
	}

	oc.lock.Lock()
	oc.connected = connected
	oc.lock.Unlock()
}
