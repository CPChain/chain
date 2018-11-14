package backend

import (
	"context"
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/signer_register"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
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

// UpdateSigners updates Handler's signers.
func (h *Handler) UpdateSigners(epochIdx uint64, signers []common.Address) error {
	h.lock.Lock()
	remoteSigners := h.signers
	h.lock.Unlock()

	for _, signer := range signers {
		if _, ok := remoteSigners[signer]; !ok {
			s := NewSigner(epochIdx, signer)
			remoteSigners[signer] = s
		}
	}

	h.lock.Lock()
	h.epochIdx = epochIdx
	h.signers = remoteSigners
	h.lock.Unlock()

	return nil
}

// DialAll connects remote signers.
func (h *Handler) DialAll() {
	h.lock.Lock()
	nodeID, address, contractInstance, auth, client := h.nodeId, h.coinbase, h.contractInstance, h.contractTransactor, h.contractCaller.Client
	connected, signers, server := h.dialed, h.signers, h.server
	rsaKey := h.rsaKey
	h.lock.Unlock()

	if !connected {
		log.Debug("connecting...")

		for _, s := range signers {
			err := s.Dial(server, nodeID, address, auth, contractInstance, client, rsaKey)
			log.Debug("err when connect", "e", err)
		}
		connected = true
	}

	h.lock.Lock()
	h.dialed = connected
	h.lock.Unlock()

}
