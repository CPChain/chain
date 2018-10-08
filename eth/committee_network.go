package eth

import (
	"context"
	"crypto/rsa"
	"errors"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/contracts/dpor/contract"
	"bitbucket.org/cpchain/chain/crypto/rsa_"
	"bitbucket.org/cpchain/chain/p2p"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/log"
)

var (
	errLengthOfSigners = errors.New("error length of signers")
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
	return err
}

// dial dials the signer.
func (rs *RemoteSigner) dial(server *p2p.Server) error {
	err := server.AddPeerFromURL(rs.nodeID)
	return err
}

func (rs *RemoteSigner) disconnect(server *p2p.Server) error {
	err := server.RemovePeerFromURL(rs.nodeID)
	return err
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

	connected bool
	lock      sync.RWMutex
}

func getRemoteSigners() []*RemoteSigner {
	return []*RemoteSigner{
		{
			nodeID:  "enode://f0946da077761c7dcbdcdbbf0d1587a5e36373150c02afb1bfadbd5713f2e894798d8c924d76874bb408ed56acf2a2112a8ae23e2730588bbc7f133a74748a45@192.168.0.117:30311",
			address: common.HexToAddress("0xE94B7b6C5A0e526A4D97f9768AD6097bdE25c62a"),
			dialed:  false,
		},
		{
			nodeID:  "enode://69038abcb206772ae36a8c04499dbc8517237d7dde23794f8f0f915f79e4b93541c4c7f8984bdc1f06f62175b89e7c019b75a7f998d191adf2d0495f1f203e95@192.168.0.117:30312",
			address: common.HexToAddress("0xc05302AceBd0730E3A18A058d7d1CB1204C4a092"),
			dialed:  false,
		},
		{
			nodeID:  "enode://18d38b205a421f78731474d64355239fc4ea75d6b768bef3db76d8275446f28a99218b51ea637817346d87d457b49d35c21cafe981f65b494ba5638298c400da@192.168.0.117:30313",
			address: common.HexToAddress("0xEF3dd127DE235F15ffB4FC0D71469d1339DF6465"),
			dialed:  false,
		},
		{
			nodeID:  "enode://2eb4b8b71e95037e35e1e7a1e86fb00ebfced18dd84f82a092bf9392969db319cfd47fdbc96f03ca989f489482ee626b95eac85839613597904b99792f4af661@192.168.0.117:30314",
			address: common.HexToAddress("0x3A18598184eF84198Db90C28FdfDfDF56544f747"),
			dialed:  false,
		},
		{
			nodeID:  "enode://21223195c1e1dfede63be02083067c3454d3ed8ad13bee948e11f6f440031631fca92911f743d16a3a5bf18882fbbb15f1d5929cfa08b8539963584c82beae02@192.168.0.117:30315",
			address: common.HexToAddress("0x6E31e5B68A98dcD17264bd1ba547D0B3E874dA1E"),
			dialed:  false,
		},
	}
}

// NewBasicCommitteeNetworkHandler creates a BasicCommitteeNetworkHandler instance
func NewBasicCommitteeNetworkHandler(peers *peerSet, epochLength uint64, ownAddress common.Address, contractAddress common.Address, server *p2p.Server) (*BasicCommitteeNetworkHandler, error) {
	bc := &BasicCommitteeNetworkHandler{
		// peers:           peers,
		server: server,
		// ownNodeID:       server.Self().String(),
		// ownPubkey:       server.RsaPublicKeyBytes,
		// ownAddress:      ownAddress,
		// contractAddress: contractAddress,
		// remoteSigners:   make([]*RemoteSigner, epochLength-1),
		remoteSigners: getRemoteSigners(),
		connected:     true,
	}
	return bc, nil
}

// UpdateContractCaller updates contractcaller.
func (oc *BasicCommitteeNetworkHandler) UpdateContractCaller(contractCaller *dpor.ContractCaller) error {
	oc.contractCaller = contractCaller
	contractInstance, err := contract.NewSignerConnectionRegister(oc.contractAddress, oc.contractCaller.Client)
	if err != nil {
		return err
	}
	oc.contractInstance = contractInstance

	auth := bind.NewKeyedTransactor(oc.contractCaller.Key.PrivateKey)
	auth.Value = big.NewInt(0)
	auth.GasLimit = oc.contractCaller.GasLimit
	auth.GasPrice = big.NewInt(int64(oc.contractCaller.GasPrice))

	oc.contractTransacter = auth

	return nil
}

// UpdateRemoteSigners updates BasicCommitteeNetworkHandler's remoteSigners.
func (oc *BasicCommitteeNetworkHandler) UpdateRemoteSigners(epochIdx uint64, signers []common.Address) error {
	oc.epochIdx = epochIdx

	if len(signers) != len(oc.remoteSigners) {
		return errLengthOfSigners
	}
	for _, signer := range signers {
		s := NewRemoteSigner(epochIdx, signer)
		oc.remoteSigners = append(oc.remoteSigners, s)
	}
	return nil
}

func (oc *BasicCommitteeNetworkHandler) Connect() {
	if !oc.connected {
		log.Info("connecting...")
		// 	for _, s := range oc.remoteSigners {
		// 		err := s.dial(oc.server)
		// 		log.Info("err when connect", "e", err)
		// 	}
		oc.connected = true
	}
}
func (oc *BasicCommitteeNetworkHandler) Disconnect() {
	if oc.connected {
		log.Info("disconnecting...")
		// 	for _, s := range oc.remoteSigners {
		// 		err := s.disconnect(oc.server)
		// 		log.Info("err when disconnect", "e", err)
		// 	}
		oc.connected = false
	}
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
