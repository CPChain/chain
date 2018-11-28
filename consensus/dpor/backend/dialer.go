package backend

import (
	"context"
	"encoding/hex"
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/signer_register"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
)

// SetServer sets handler.server
func (h *Handler) SetServer(server *p2p.Server) error {
	h.lock.Lock()
	defer h.lock.Unlock()

	h.server = server
	h.nodeId = server.Self().String()

	return nil
}

// SetRsaKey sets handler.rsaKey
func (h *Handler) SetRsaKey(rsaReader RsaReader) error {
	h.lock.Lock()
	defer h.lock.Unlock()

	var err error
	h.rsaKey, err = rsaReader()

	return err
}

// SetContractCaller sets handler.contractcaller.
func (h *Handler) SetContractCaller(contractCaller *ContractCaller) error {

	// creates an contract instance
	contractInstance, err := contract.NewSignerConnectionRegister(h.contractAddress, contractCaller.Client)
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

	rsaReader := func() (*rsakey.RsaKey, error) {
		return contractCaller.Key.RsaKey, nil
	}
	err = h.SetRsaKey(rsaReader)
	if err != nil {
		return err
	}

	h.lock.Lock()

	// assign
	h.contractCaller = contractCaller
	h.contractInstance = contractInstance
	h.contractTransactor = auth

	h.lock.Unlock()

	return nil
}

// UpdateRemoteProposers updates Handler's signers.
func (h *Handler) UpdateRemoteProposers(epochIdx uint64, signers []common.Address) error {
	h.lock.Lock()
	defer h.lock.Unlock()

	remoteProposers := h.remoteProposers
	for _, signer := range signers {
		if _, ok := remoteProposers[signer]; !ok {
			s := NewRemoteProposer(epochIdx, signer)
			remoteProposers[signer] = s
		}
	}

	h.term = epochIdx
	h.remoteProposers = remoteProposers

	return nil
}

// UpdateRemoteValidators updates Handler's signers.
func (h *Handler) UpdateRemoteValidators(epochIdx uint64, signers []common.Address) error {
	h.lock.Lock()
	defer h.lock.Unlock()

	remoteSigners := h.remoteValidators
	for _, signer := range signers {
		if _, ok := remoteSigners[signer]; !ok {
			s := NewRemoteValidator(epochIdx, signer)
			remoteSigners[signer] = s
		}
	}

	h.term = epochIdx
	h.remoteValidators = remoteSigners

	return nil
}

// DialAllRemoteProposers dials all remote proposers
func (h *Handler) DialAllRemoteProposers() error {

	h.lock.Lock()
	rsaKey, server := h.rsaKey, h.server
	contractInstance := h.contractInstance
	h.lock.Unlock()

	log.Debug("connecting...")
	signers := h.remoteProposers

	for _, s := range signers {
		_, err := s.fetchNodeInfoAndDial(server, rsaKey, contractInstance)
		if err != nil {
			return err
		}
	}

	return nil
}

// UploadEncryptedNodeInfo dials all remote validators
func (h *Handler) UploadEncryptedNodeInfo() error {

	h.lock.Lock()
	nodeID, address := h.nodeId, h.coinbase
	contractInstance, contractTransactor, client := h.contractInstance, h.contractTransactor, h.contractCaller.Client
	h.lock.Unlock()

	log.Debug("connecting...")
	signers := h.remoteValidators

	for _, s := range signers {
		_, err := s.uploadNodeInfo(nodeID, address, contractTransactor, contractInstance, client)
		if err != nil {
			return err
		}
	}

	return nil
}

// fetchPubkey fetches the public key of the remote signer from the contract.
func (s *RemoteSigner) fetchPubkey(contractInstance *contract.SignerConnectionRegister) error {

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
func (s *RemoteSigner) fetchNodeID(contractInstance *contract.SignerConnectionRegister, rsaKey *rsakey.RsaKey) error {
	epochIdx, address := s.epochIdx, s.address

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
	s.nodeID = nodeID
	s.nodeIDFetched = true

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

// uploadNodeID encrypts my node id with this remote signer's public key and update to the contract.
func (s *RemoteSigner) uploadNodeID(nodeID string, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client ClientBackend) error {
	epochIdx, address := s.epochIdx, s.address

	log.Debug("fetched rsa pubkey")
	log.Debug(hex.Dump(s.pubkey))

	pubkey, err := rsakey.NewRsaPublicKey(s.pubkey)

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

	s.nodeIDUpdated = true

	log.Debug("updated self nodeID")

	return nil
}

// uploadNodeInfo upload my nodeID the signer.
func (s *RemoteSigner) uploadNodeInfo(
	nodeID string,
	address common.Address,
	auth *bind.TransactOpts,
	contractInstance *contract.SignerConnectionRegister,
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

	nodeid, err := fetchNodeID(s.epochIdx, address, contractInstance)
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
	contractInstance *contract.SignerConnectionRegister,
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
func (s *RemoteSigner) Dial(server *p2p.Server, nodeID string, address common.Address, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client ClientBackend, rsaKey *rsakey.RsaKey) (bool, error) {

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
