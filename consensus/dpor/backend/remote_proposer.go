package backend

import (
	"encoding/hex"

	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	dpor "bitbucket.org/cpchain/chain/contracts/dpor/contracts"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
)

// RemoteProposer represents a remote proposer waiting to be connected.
type RemoteProposer struct {
	*RemoteSigner
}

// NewRemoteProposer creates a new remote proposer
func NewRemoteProposer(term uint64, address common.Address) *RemoteProposer {
	return &RemoteProposer{
		RemoteSigner: NewRemoteSigner(term, address),
	}
}

// fetchNodeID fetches the node id of the remote signer encrypted with my public key, and decrypts it with my private key.
func (s *RemoteProposer) fetchNodeID(contractInstance *dpor.ProposerRegister, rsaKey *rsakey.RsaKey, validator common.Address) error {
	term, proposer := s.term, s.address

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
	s.nodeID = nodeID
	s.nodeIDFetched = true

	log.Debug("fetched nodeID of remote signer", "nodeID", nodeID)

	return nil
}

func (s *RemoteProposer) FetchNodeInfoAndDial(
	validator common.Address,
	server *p2p.Server,
	rsaKey *rsakey.RsaKey,
	contractInstance *dpor.ProposerRegister,
) (bool, error) {

	// fetch the nodeID of the remote signer if not fetched yet.
	if !s.nodeIDFetched {
		err := s.fetchNodeID(contractInstance, rsaKey, validator)
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
