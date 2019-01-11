package backend

import (
	"encoding/hex"
	"sync"

	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/proposer_register"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
)

// RemoteProposer represents a remote proposer waiting to be connected.
type RemoteProposer struct {
	*RemoteSigner

	nodeID string
	dialed bool // bool to show if i already connected to this signer.

	proposerLock sync.RWMutex
}

// NewRemoteProposer creates a new remote proposer
func NewRemoteProposer(address common.Address) *RemoteProposer {
	return &RemoteProposer{
		RemoteSigner: NewRemoteSigner(address),
	}
}

// Dialed returns if already dialed the remote proposer
func (s *RemoteProposer) Dialed() bool {
	s.proposerLock.RLock()
	defer s.proposerLock.RUnlock()

	return s.dialed
}

// ToggleDialed toggles dialed
func (s *RemoteProposer) ToggleDialed() {
	s.proposerLock.Lock()
	defer s.proposerLock.Unlock()

	s.dialed = !s.dialed
}

func (s *RemoteProposer) getNodeID() string {
	s.proposerLock.RLock()
	defer s.proposerLock.RUnlock()

	return s.nodeID
}

func (s *RemoteProposer) setNodeID(nodeID string) {
	s.proposerLock.Lock()
	defer s.proposerLock.Unlock()

	s.nodeID = nodeID
}

// fetchNodeID fetches the node id of the remote signer encrypted with my public key, and decrypts it with my private key.
func (s *RemoteProposer) fetchNodeID(term uint64, contractInstance *proposer_register.ProposerRegister, rsaKey *rsakey.RsaKey, validator common.Address) error {
	proposer := s.Coinbase()

	log.Debug("fetching nodeID of remote proposer")
	log.Debug("term", "term", term)
	log.Debug("proposer", "addr", proposer.Hex())

	encryptedNodeID, err := fetchNodeID(term, proposer, validator, contractInstance)
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
	s.setNodeID(nodeID)

	log.Debug("fetched nodeID of remote signer", "nodeID", nodeID)

	return nil
}

// FetchNodeInfoAndDial fetches remote proposer's nodeID from contract and dial with it
func (s *RemoteProposer) FetchNodeInfoAndDial(
	term uint64,
	validator common.Address,
	server *p2p.Server,
	rsaKey *rsakey.RsaKey,
	contractInstance *proposer_register.ProposerRegister,
) (bool, error) {

	// fetch the nodeID of the remote signer if not fetched yet.
	if len(s.getNodeID()) == 0 {
		err := s.fetchNodeID(term, contractInstance, rsaKey, validator)
		if err != nil {
			log.Warn("err when fetching signer's nodeID from contract", "err", err)
			return false, err
		}
	}

	// dial the signer with his nodeID if not dialed yet.
	if len(s.getNodeID()) != 0 && !s.Dialed() {
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
		s.ToggleDialed()
	}

	return s.Dialed(), nil
}
