package eth

import (
	"context"
	"crypto/rsa"
	"errors"

	"math/big"
	"sync"

	"github.com/ethereum/go-ethereum/accounts/abi/bind"

	"github.com/ethereum/go-ethereum/crypto/rsa_"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus/dpor"
	"github.com/ethereum/go-ethereum/contracts/dpor/contract"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/p2p"
)

// RemoteSigner represents a remote signer waiting to be connected and communicate with.
type RemoteSigner struct {
	epochIdx uint64
	pubkey   []byte
	nodeID   string
	address  common.Address
	updated  bool // bool to show if i updated my nodeid encrypted with this signer's pubkey to the contract.
	dialed   bool // bool to show if i already connected to this signer.

	lock sync.RWMutex
}

// NewRemoteSigner creates a new NewRemoteSigner with given view idx and address.
func NewRemoteSigner(epochIdx uint64, address common.Address) *RemoteSigner {
	return &RemoteSigner{
		epochIdx: epochIdx,
		address:  address,
		updated:  false,
		dialed:   false,
	}
}

// fetchPubkey fetches the public key of the remote signer from the contract.
func (rs *RemoteSigner) fetchPubkey(contractInstance *contract.SignerConnectionRegister) ([]byte, error) {
	pubkey, err := contractInstance.GetPublicKey(nil, rs.address)
	if err != nil {
		return nil, err
	}
	return pubkey, nil
}

// fetchNodeID fetches the node id of the remote signer encrypted with my public key, and decrypts it with my private key.
func (rs *RemoteSigner) fetchNodeID(contractInstance *contract.SignerConnectionRegister, privKey *rsa.PrivateKey) (string, error) {
	encryptedNodeID, err := contractInstance.GetNodeInfo(nil, big.NewInt(int64(rs.epochIdx)), rs.address)
	if err != nil {
		return "", err
	}
	nodeID, err := rsa_.RsaDecrypt(encryptedNodeID, privKey)
	if err != nil {
		return "", err
	}
	return string(nodeID), nil
}

// updateNodeID encrypts my node id with this remote signer's public key and update to the contract.
func (rs *RemoteSigner) updateNodeID(nodeID string, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client dpor.ClientBackend) error {
	pubkey, err := rsa_.Bytes2PublicKey(rs.pubkey)
	if err != nil {
		return err
	}
	encryptedNodeID, err := rsa_.RsaEncrypt([]byte(nodeID), pubkey)
	transaction, err := contractInstance.AddNodeInfo(auth, big.NewInt(int64(rs.epochIdx)), rs.address, encryptedNodeID)
	if err != nil {
		return err
	}
	ctx := context.Background()
	_, err = bind.WaitMined(ctx, client, transaction)
	if err != nil {
		return err
	}
	return nil
}

// dial dials the signer.
func (rs *RemoteSigner) dial(server *p2p.Server) error {
	err := server.AddPeerFromURL(string(rs.nodeID))
	if err != nil {
		return err
	}
	return nil
}

// BasicCommitteeNetworkHandler implements CommitteeNetworkHandler
type BasicCommitteeNetworkHandler struct {
	peers *peerSet

	epochIdx uint64

	ownNodeID  string
	ownPubkey  []byte
	ownAddress common.Address

	server *p2p.Server

	contractAddress    common.Address
	contractCaller     *dpor.ContractCaller
	contractInstance   *contract.SignerConnectionRegister
	contractTransacter *bind.TransactOpts

	remoteSigners []*RemoteSigner
}

// NewBasicCommitteeNetworkHandler creates a BasicCommitteeNetworkHandler instance
func NewBasicCommitteeNetworkHandler(peers *peerSet, epochIdx uint64, epochLength uint64, ownNodeID string, ownPubkey []byte, ownAddress common.Address, server *p2p.Server, contractAddress common.Address, contractCaller *dpor.ContractCaller) (*BasicCommitteeNetworkHandler, error) {
	bc := &BasicCommitteeNetworkHandler{
		peers:      peers,
		server:     server,
		epochIdx:   epochIdx,
		ownNodeID:  ownNodeID,
		ownPubkey:  ownPubkey,
		ownAddress: ownAddress,

		contractAddress: contractAddress,
		contractCaller:  contractCaller,

		remoteSigners: make([]*RemoteSigner, epochLength-1),
	}

	contractInstance, err := contract.NewSignerConnectionRegister(bc.contractAddress, bc.contractCaller.Client)
	if err != nil {
		return nil, err
	}
	bc.contractInstance = contractInstance

	auth := bind.NewKeyedTransactor(bc.server.PrivateKey)
	auth.Value = big.NewInt(0)
	auth.GasLimit = bc.contractCaller.GasLimit
	auth.GasPrice = big.NewInt(int64(bc.contractCaller.GasPrice))

	bc.contractTransacter = auth

	return bc, nil
}

// UpdateRemoteSigners updates BasicCommitteeNetworkHandler's remoteSigners.
func (oc *BasicCommitteeNetworkHandler) UpdateRemoteSigners(epochIdx uint64, signers []common.Address) error {
	oc.epochIdx = epochIdx

	if len(signers) != len(oc.remoteSigners) {
		return errors.New("error length of signer")
	}
	for _, signer := range signers {
		s := NewRemoteSigner(epochIdx, signer)
		oc.remoteSigners = append(oc.remoteSigners, s)
	}
	return nil
}

// Handle implements CommitteeNetworkHandler.Handle
func (oc *BasicCommitteeNetworkHandler) Handle() {

	// TODO: add lock, go rountine this! Liu Qian
	err := oc.FetchPubKey()
	if err != nil {
		log.Warn("error when fetching remote signers' pubkey", "err", "err")
	}

	err = oc.UpdateNodeID()
	if err != nil {
		log.Warn("error when updating self nodeID encrypted with remote signers' pubkey", "err", "err")
	}

	err = oc.FetchNodeID()
	if err != nil {
		log.Warn("error when fetching remote signers' nodeIDs", "err", "err")
	}

	err = oc.DialRemote()
	if err != nil {
		log.Warn("error when dialing to remote signers", "err", "err")
	}
}

// FetchPubKey implements CommitteeNetworkHandler.FetchPubKey
func (oc *BasicCommitteeNetworkHandler) FetchPubKey() error {

	for idx, signer := range oc.remoteSigners {
		if len(signer.pubkey) > 0 {
			continue
		}
		pubkey, err := signer.fetchPubkey(oc.contractInstance)
		if err != nil {
			log.Warn("error when fetch pubkey of", "address", signer.address)
			log.Warn("error when fetch pubkey ", "error", err)
			continue
			// return err
		}
		oc.remoteSigners[idx].pubkey = pubkey
		log.Debug("fetched pubkey of", "address", signer.address)
		log.Debug("fetched pubkey ", "pubkey", signer.pubkey)
	}
	return nil
}

// UpdateNodeID implements CommitteeNetworkHandler.UpdateNodeID
func (oc *BasicCommitteeNetworkHandler) UpdateNodeID() error {

	for idx, signer := range oc.remoteSigners {
		if len(signer.pubkey) == 0 {
			// TODO: go routine to fetch signer.pubkey.
			continue
		}
		if signer.updated {
			continue
		}
		err := signer.updateNodeID(oc.ownNodeID, oc.contractTransacter, oc.contractInstance, oc.contractCaller.Client)
		if err != nil {
			log.Warn("error when update self nodeID encrypted with remote signer's public", "address", signer.address)
			log.Warn("error", "error", err)
			continue
			// return err
		}
		oc.remoteSigners[idx].updated = true
	}

	return nil
}

// FetchNodeID implements CommitteeNetworkHandler.FetchNodeID
func (oc *BasicCommitteeNetworkHandler) FetchNodeID() error {

	for idx, signer := range oc.remoteSigners {
		if len(signer.nodeID) > 0 {
			continue
		}
		nodeID, err := signer.fetchNodeID(oc.contractInstance, oc.server.RsaPrivateKey)
		if err != nil {
			log.Warn("error when update self nodeID encrypted with remote signer's public", "address", signer.address)
			log.Warn("error", "error", err)
			continue
			// return err

		}
		oc.remoteSigners[idx].nodeID = nodeID
	}

	return nil
}

// DialRemote implements CommitteeNetworkHandler.DialRemote
func (oc *BasicCommitteeNetworkHandler) DialRemote() (err error) {
	for _, signer := range oc.remoteSigners {
		if len(signer.nodeID) == 0 {
			// TODO: go routine to fetch signer.nodeID.
			continue
		}
		err := signer.dial(oc.server)
		if err != nil {
			log.Warn("error when dial remote signer", "nodeID", signer.nodeID)
			log.Warn("error", "error", err)
			// return err
		}
	}
	return nil
}
