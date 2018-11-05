package backend

import (
	"context"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/signerRegister"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

// Handler implements PbftHandler
type Handler struct {
	connected bool
	epochIdx  uint64

	ownNodeID  string
	ownAddress common.Address

	server *p2p.Server
	RsaKey *rsakey.RsaKey

	contractAddress    common.Address
	contractCaller     *ContractCaller
	contractInstance   *contract.SignerConnectionRegister
	contractTransactor *bind.TransactOpts

	signers map[common.Address]*Signer

	lock sync.RWMutex
}

// New creates a PbftHandler
func New(config *configs.DporConfig, etherbase common.Address) (*Handler, error) {
	ch := &Handler{
		ownAddress:      etherbase,
		contractAddress: config.Contracts["signer"],
		signers:         make(map[common.Address]*Signer),
		connected:       false,
	}
	return ch, nil
}

// SetServer sets handler.server
func (ch *Handler) SetServer(server *p2p.Server) error {
	ch.lock.Lock()
	defer ch.lock.Unlock()

	ch.server = server
	ch.ownNodeID = server.Self().String()

	return nil
}

// SetRsaKey sets handler.rsaKey
func (ch *Handler) SetRsaKey(rsaReader RsaReader) error {
	ch.lock.Lock()
	defer ch.lock.Unlock()

	var err error
	ch.RsaKey, err = rsaReader()

	return err
}

// SetContractCaller sets handler.contractcaller.
func (ch *Handler) SetContractCaller(contractCaller *ContractCaller) error {

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

// UpdateSigners updates Handler's signers.
func (ch *Handler) UpdateSigners(epochIdx uint64, signers []common.Address) error {
	ch.lock.Lock()
	remoteSigners := ch.signers
	ch.lock.Unlock()

	for _, signer := range signers {
		if _, ok := remoteSigners[signer]; !ok {
			s := NewSigner(epochIdx, signer)
			remoteSigners[signer] = s
		}
	}

	ch.lock.Lock()
	ch.epochIdx = epochIdx
	ch.signers = remoteSigners
	ch.lock.Unlock()

	return nil
}

// DialAll connects remote signers.
func (ch *Handler) DialAll() {
	ch.lock.Lock()
	nodeID, address, contractInstance, auth, client := ch.ownNodeID, ch.ownAddress, ch.contractInstance, ch.contractTransactor, ch.contractCaller.Client
	connected, signers, server := ch.connected, ch.signers, ch.server
	rsaKey := ch.RsaKey
	ch.lock.Unlock()

	if !connected {
		log.Debug("connecting...")

		for _, s := range signers {
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
func (ch *Handler) Disconnect() {
	ch.lock.Lock()
	connected, signers, server := ch.connected, ch.signers, ch.server
	ch.lock.Unlock()

	if connected {
		log.Debug("disconnecting...")

		for _, s := range signers {
			err := s.disconnect(server)
			log.Debug("err when disconnect", "e", err)
		}

		ch.connected = false
	}

	ch.lock.Lock()
	ch.connected = connected
	ch.lock.Unlock()
}

// Start starts pbft handler
func (ch *Handler) Start() error {
	return nil
}

// Stop stops all
func (ch *Handler) Stop() error {
	return nil
}

// SendMsg sends msg to signer with given addr
func (ch *Handler) SendMsg(addr common.Address, msg interface{}) error {
	return nil
}

// BroadcastMsg broadcasts msg to all
func (ch *Handler) BroadcastMsg(msg interface{}) error {
	return nil
}
