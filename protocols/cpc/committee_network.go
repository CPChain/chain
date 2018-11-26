// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package cpc

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
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/signer_register"
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
func (rs *RemoteSigner) fetchPubkey(contractInstance *signer_register.SignerConnectionRegister) error {

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
func (rs *RemoteSigner) fetchNodeID(contractInstance *signer_register.SignerConnectionRegister, rsaKey *rsakey.RsaKey) error {
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

func fetchNodeID(epochIdx uint64, address common.Address, contractInstance *signer_register.SignerConnectionRegister) ([]byte, error) {
	encryptedNodeID, err := contractInstance.GetNodeInfo(nil, big.NewInt(int64(epochIdx)), address)
	if err != nil {
		return nil, err
	}
	return encryptedNodeID, nil
}

// updateNodeID encrypts my node id with this remote signer's public key and update to the contract.
func (rs *RemoteSigner) updateNodeID(nodeID string, auth *bind.TransactOpts, contractInstance *signer_register.SignerConnectionRegister, client consensus.ClientBackend) error {
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
func (rs *RemoteSigner) dial(server *p2p.Server, nodeID string, address common.Address, auth *bind.TransactOpts, contractInstance *signer_register.SignerConnectionRegister, client consensus.ClientBackend, rsaKey *rsakey.RsaKey) (bool, error) {
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

func (rs *RemoteSigner) Dial(server *p2p.Server, nodeID string, address common.Address, auth *bind.TransactOpts, contractInstance *signer_register.SignerConnectionRegister, client consensus.ClientBackend, rsaKey *rsakey.RsaKey) error {

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

// BasicCommitteeHandler implements consensus.CommitteeHandler
type BasicCommitteeHandler struct {
	epochIdx uint64

	ownNodeID  string
	ownAddress common.Address

	server *p2p.Server

	contractAddress    common.Address
	contractCaller     *consensus.ContractCaller
	contractInstance   *signer_register.SignerConnectionRegister
	contractTransactor *bind.TransactOpts

	RsaKey *rsakey.RsaKey

	remoteSigners []*RemoteSigner

	connected bool
	lock      sync.RWMutex
}

// NewBasicCommitteeNetworkHandler creates a BasicCommitteeNetworkHandler instance
func NewBasicCommitteeNetworkHandler(config *configs.DporConfig, cpcbase common.Address) (*BasicCommitteeHandler, error) {
	bc := &BasicCommitteeHandler{
		ownAddress:      cpcbase,
		contractAddress: config.Contracts[configs.ContractProposer],
		remoteSigners:   make([]*RemoteSigner, config.TermLen),
		// remoteSigners:   make([]*RemoteSigner, config.Epoch-1),
		connected: false,
	}
	return bc, nil
}

func (oc *BasicCommitteeHandler) UpdateServer(server *p2p.Server) error {
	oc.lock.Lock()
	defer oc.lock.Unlock()
	oc.server = server
	oc.ownNodeID = server.Self().String()
	return nil
}

func (oc *BasicCommitteeHandler) SetRSAKeys(rsaReader RSAReader) error {
	oc.lock.Lock()
	defer oc.lock.Unlock()

	var err error

	oc.RsaKey, err = rsaReader()

	return err
}

// UpdateContractCaller updates contractcaller.
func (oc *BasicCommitteeHandler) UpdateContractCaller(contractCaller *consensus.ContractCaller) error {

	// creates an contract instance
	contractInstance, err := signer_register.NewSignerConnectionRegister(oc.contractAddress, contractCaller.Client)
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

	oc.lock.Lock()

	// assign
	oc.contractCaller = contractCaller
	oc.contractInstance = contractInstance
	oc.contractTransactor = auth

	oc.lock.Unlock()

	return nil
}

// UpdateRemoteSigners updates BasicCommitteeNetworkHandler's remoteSigners.
func (oc *BasicCommitteeHandler) UpdateRemoteSigners(epochIdx uint64, signers []common.Address) error {
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

// DialAll connects remote signers.
func (oc *BasicCommitteeHandler) DialAll() {
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
func (oc *BasicCommitteeHandler) Disconnect() {
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

// SendPreprepare implements Pbft.SendPreprepare.
func (oc *BasicCommitteeHandler) SendPreprepare(msg interface{}, broadcastFn consensus.Broadcast) error {
	go broadcastFn(msg, consensus.Preprepare)

	return nil
}

// Preprepare implements Pbft.Preprepare.
func (oc *BasicCommitteeHandler) Preprepare(msg interface{}) (bool, error) {

	return false, nil
}

// SendPrepare implements Pbft.SendPrepare.
func (oc *BasicCommitteeHandler) SendPrepare(msg interface{}, broadcastFn consensus.Broadcast) error {
	go broadcastFn(msg, consensus.Prepare)

	return nil
}

// Prepare implements Pbft.Prepare.
func (oc *BasicCommitteeHandler) Prepare(msg interface{}) (bool, error) {

	return false, nil
}

// SendCommit implements Pbft.SendCommit.
func (oc *BasicCommitteeHandler) SendCommit(msg interface{}, broadcastFn consensus.Broadcast) error {
	go broadcastFn(msg, consensus.Commit)

	return nil
}

// Commit implements Pbft.Commit.
func (oc *BasicCommitteeHandler) Commit(msg interface{}) (bool, error) {

	return false, nil
}

// Status implements Pbft.Status.
func (oc *BasicCommitteeHandler) Status() uint8 {
	return 0
}
