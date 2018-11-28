package backend

import (
	"context"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/signer_register"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

// Dialer dials a remote peer
type Dialer struct {
	term uint64

	nodeID   string
	server   *p2p.Server
	rsaKey   *rsakey.RsaKey
	coinbase common.Address

	// signer register contract related fields
	contractAddress    common.Address
	contractCaller     *ContractCaller
	contractInstance   *contract.SignerConnectionRegister
	contractTransactor *bind.TransactOpts

	remoteProposers  map[common.Address]*RemoteProposer
	remoteValidators map[common.Address]*RemoteValidator

	dialed bool

	lock           sync.RWMutex
	proposersLock  sync.RWMutex
	validatorsLock sync.RWMutex
}

func newDialer(
	coinbase common.Address,
	proposers map[common.Address]*RemoteProposer,
	validators map[common.Address]*RemoteValidator,
) *Dialer {

	return &Dialer{
		coinbase:         coinbase,
		remoteProposers:  proposers,
		remoteValidators: validators,
	}
}

// AddPeer adds a peer to local dpor peer set:
// remote proposers or remote validators
func (d *Dialer) AddPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter, coinbase common.Address, verifyFn VerifyRemoteValidatorFn) (string, bool, error) {

	log.Debug("do handshaking with remote peer...")

	// TODO: add signer handshake to determine whether validator handshake
	// or proposer handshake

	ok, address, err := ValidatorHandshake(p, rw, coinbase, verifyFn)
	if !ok || err != nil {
		log.Debug("failed to handshake in dpor", "err", err, "ok", ok)
		return "", ok, err
	}
	remoteValidator, err := d.addRemoteValidator(version, p, rw, address)
	log.Debug("after add remote validator", "validator", remoteValidator.ID(), "err", err)
	return address.Hex(), true, err
}

func (d *Dialer) addRemoteValidator(version int, p *p2p.Peer, rw p2p.MsgReadWriter, address common.Address) (*RemoteValidator, error) {
	remoteValidator, ok := d.getValidator(address.Hex())
	if !ok {
		remoteValidator = NewRemoteValidator(d.term, address)
	}

	log.Debug("adding remote validator...", "validator", address.Hex())

	err := remoteValidator.SetPeer(version, p, rw)
	if err != nil {
		log.Debug("failed to set remote validator")
		return nil, err
	}

	err = remoteValidator.AddStatic(d.server)
	if err != nil {
		log.Debug("failed to add remote validator as static peer")
		return nil, err
	}

	go remoteValidator.broadcastLoop()

	d.setValidator(address.Hex(), remoteValidator)
	return remoteValidator, nil
}

func (d *Dialer) removeRemoteValidator(addr string) error {
	d.validatorsLock.Lock()
	defer d.validatorsLock.Unlock()

	address := common.HexToAddress(addr)
	if _, ok := d.remoteValidators[address]; ok {
		delete(d.remoteValidators, address)
	}

	return nil
}

// SetServer sets dialer.server
func (d *Dialer) SetServer(server *p2p.Server) error {
	d.lock.Lock()
	defer d.lock.Unlock()

	d.server = server
	d.nodeID = server.Self().String()

	return nil
}

// SetRsaKey sets handler.rsaKey
func (d *Dialer) SetRsaKey(rsaReader RsaReader) error {
	d.lock.Lock()
	defer d.lock.Unlock()

	var err error
	d.rsaKey, err = rsaReader()

	return err
}

// SetContractCaller sets dialer.contractcaller.
func (d *Dialer) SetContractCaller(contractCaller *ContractCaller) error {

	// creates an contract instance
	contractInstance, err := contract.NewSignerConnectionRegister(d.contractAddress, contractCaller.Client)
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
	err = d.SetRsaKey(rsaReader)
	if err != nil {
		return err
	}

	d.lock.Lock()

	// assign
	d.contractCaller = contractCaller
	d.contractInstance = contractInstance
	d.contractTransactor = auth

	d.lock.Unlock()

	return nil
}

// UpdateRemoteProposers updates dialer.remoteProposers.
func (d *Dialer) UpdateRemoteProposers(epochIdx uint64, signers []common.Address) error {
	d.lock.Lock()
	d.term = epochIdx
	d.lock.Unlock()

	for _, signer := range signers {
		if _, ok := d.getProposer(signer.Hex()); !ok {
			s := NewRemoteProposer(epochIdx, signer)
			d.setProposer(signer.Hex(), s)
		}
	}

	return nil
}

// UpdateRemoteValidators updates dialer.remoteValidators.
func (d *Dialer) UpdateRemoteValidators(epochIdx uint64, signers []common.Address) error {
	d.lock.Lock()
	d.term = epochIdx
	d.lock.Unlock()

	for _, signer := range signers {
		if _, ok := d.getValidator(signer.Hex()); !ok {
			s := NewRemoteValidator(epochIdx, signer)
			d.setValidator(signer.Hex(), s)
		}
	}

	return nil
}

// DialAllRemoteProposers dials all remote proposers
func (d *Dialer) DialAllRemoteProposers() error {

	d.lock.RLock()
	rsaKey, server := d.rsaKey, d.server
	contractInstance := d.contractInstance
	d.lock.RUnlock()

	d.proposersLock.RLock()
	signers := d.remoteProposers
	d.proposersLock.RUnlock()

	for _, s := range signers {
		_, err := s.fetchNodeInfoAndDial(server, rsaKey, contractInstance)
		if err != nil {
			return err
		}
	}

	return nil
}

// UploadEncryptedNodeInfo dials all remote validators
func (d *Dialer) UploadEncryptedNodeInfo() error {

	d.lock.RLock()
	nodeID, address := d.nodeID, d.coinbase
	contractInstance, contractTransactor, client := d.contractInstance, d.contractTransactor, d.contractCaller.Client
	d.lock.RUnlock()

	d.validatorsLock.RLock()
	signers := d.remoteValidators
	d.validatorsLock.RUnlock()

	for _, s := range signers {
		_, err := s.uploadNodeInfo(nodeID, address, contractTransactor, contractInstance, client)
		if err != nil {
			return err
		}
	}

	return nil
}

// Disconnect disconnects all proposers.
func (d *Dialer) Disconnect() {
	d.lock.RLock()
	connected, server := d.dialed, d.server
	d.lock.RUnlock()

	d.proposersLock.RLock()
	remoteProposer := d.remoteProposers
	d.proposersLock.RUnlock()

	if connected {
		log.Debug("disconnecting...")

		for _, s := range remoteProposer {
			err := s.disconnect(server)
			log.Debug("err when disconnect", "e", err)
		}

		connected = false
	}

	d.lock.Lock()
	d.dialed = connected
	d.lock.Unlock()
}

func (d *Dialer) getProposer(addr string) (*RemoteProposer, bool) {
	d.proposersLock.RLock()
	defer d.proposersLock.RUnlock()

	if rv, ok := d.remoteProposers[common.HexToAddress(addr)]; ok {
		return rv, true
	}
	return nil, false
}

func (d *Dialer) setProposer(addr string, proposer *RemoteProposer) {
	d.proposersLock.Lock()
	defer d.proposersLock.Unlock()

	d.remoteProposers[common.HexToAddress(addr)] = proposer
}

func (d *Dialer) getValidator(addr string) (*RemoteValidator, bool) {
	d.validatorsLock.RLock()
	defer d.validatorsLock.RUnlock()

	if rv, ok := d.remoteValidators[common.HexToAddress(addr)]; ok {
		return rv, true
	}
	return nil, false
}

func (d *Dialer) setValidator(addr string, validator *RemoteValidator) {
	d.validatorsLock.Lock()
	defer d.validatorsLock.Unlock()

	d.remoteValidators[common.HexToAddress(addr)] = validator
}
