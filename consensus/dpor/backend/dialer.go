package backend

import (
	"context"
	"math/big"
	"sync"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	lru "github.com/hashicorp/golang-lru"
)

const (
	maxTermsOfRemoteSigners = 10
)

// Dialer dials a remote peer
type Dialer struct {
	currentTerm uint64

	nodeID   string
	server   *p2p.Server
	rsaKey   *rsakey.RsaKey
	coinbase common.Address

	dpor DporService

	// proposer register contract related fields
	contractAddress    common.Address
	contractCaller     *ContractCaller
	contractInstance   *dpor.ProposerRegister
	contractTransactor *bind.TransactOpts

	// use lru caches to cache recent proposers and validators
	recentProposers  *lru.ARCCache
	recentValidators *lru.ARCCache

	lock           sync.RWMutex // to protect basic fields
	proposersLock  sync.RWMutex // to protect recent proposers
	validatorsLock sync.RWMutex // to protect recent validators
}

// NewDialer creates a new dialer to dial remote peers
func NewDialer(
	coinbase common.Address,
	contractAddr common.Address,
) *Dialer {

	proposers, _ := lru.NewARC(maxTermsOfRemoteSigners)
	validators, _ := lru.NewARC(maxTermsOfRemoteSigners)

	return &Dialer{
		coinbase:         coinbase,
		contractAddress:  contractAddr,
		recentProposers:  proposers,
		recentValidators: validators,
	}
}

func (d *Dialer) SetDporService(dpor DporService) {
	d.dpor = dpor
}

// AddPeer adds a peer to local dpor peer set:
// remote proposers or remote validators
func (d *Dialer) AddPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter, coinbase common.Address, term uint64, futureTerm uint64) (string, bool, bool, error) {
	address, isProposer, isValidator, err := d.addPeer(version, p, rw, coinbase, term, futureTerm)
	return address, isProposer, isValidator, err
}

func (d *Dialer) addPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter, coinbase common.Address, term uint64, futureTerm uint64) (string, bool, bool, error) {

	log.Debug("do handshaking with remote peer...")

	address, err := Handshake(p, rw, coinbase, term, futureTerm)

	isProposer, isValidator := true, true

	// isProposer, isValidator := false, false
	// for t := term; t <= futureTerm; t++ {
	// 	isP, _ := d.dpor.VerifyProposerOf(address, t)
	// 	isV, _ := d.dpor.VerifyValidatorOf(address, t)

	// 	isProposer = isProposer || isP
	// 	isValidator = isValidator || isV
	// }

	if (!isProposer && !isValidator) || err != nil {
		log.Debug("failed to handshake in dpor", "err", err, "isProposer", isProposer, "isValidator", isValidator)
		return "", isProposer, isValidator, err
	}

	if isProposer {
		remoteProposer, err := d.addRemoteProposer(version, p, rw, address, term)
		log.Debug("after add remote proposer", "proposer", remoteProposer.ID(), "err", err)

	}

	if isValidator {
		remoteValidator, err := d.addRemoteValidator(version, p, rw, address, term)
		log.Debug("after add remote validator", "validator", remoteValidator.ID(), "err", err)
	}
	return address.Hex(), isProposer, isValidator, err
}

// addRemoteProposer adds a p2p peer to local proposers set
func (d *Dialer) addRemoteProposer(version int, p *p2p.Peer, rw p2p.MsgReadWriter, address common.Address, term uint64) (*RemoteProposer, error) {
	remoteProposer, ok := d.getProposer(address.Hex())
	if !ok {
		remoteProposer = NewRemoteProposer(address)
	}

	log.Debug("adding remote proposer...", "proposer", address.Hex())

	err := remoteProposer.SetPeer(version, p, rw)
	if err != nil {
		log.Debug("failed to set remote proposer")
		return nil, err
	}

	err = remoteProposer.AddStatic(d.server)
	if err != nil {
		log.Debug("failed to add remote proposer as static peer")
		return nil, err
	}

	d.setProposer(address.Hex(), remoteProposer)
	return remoteProposer, nil
}

// addRemoteValidator adds a p2p peer to local validators set
func (d *Dialer) addRemoteValidator(version int, p *p2p.Peer, rw p2p.MsgReadWriter, address common.Address, term uint64) (*RemoteValidator, error) {
	remoteValidator, ok := d.getValidator(address.Hex())
	if !ok {
		remoteValidator = NewRemoteValidator(term, address)
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

// removeRemoteProposers removes remote proposer by it's addr
func (d *Dialer) removeRemoteProposers(addr string) error {
	d.proposersLock.Lock()
	defer d.proposersLock.Unlock()

	d.recentProposers.Remove(addr)
	return nil
}

// removeRemoteValidators removes remote proposer by it's addr
func (d *Dialer) removeRemoteValidators(addr string) error {
	d.validatorsLock.Lock()
	defer d.validatorsLock.Unlock()

	d.recentValidators.Remove(addr)
	return nil
}

// SetServer sets dialer.server
func (d *Dialer) SetServer(server *p2p.Server) error {
	d.lock.Lock()
	d.server = server
	d.lock.Unlock()

	nodeID := server.Self().String()
	d.SetNodeID(nodeID)

	return nil
}

// SetNodeID sets dialer.nodeID
func (d *Dialer) SetNodeID(nodeID string) {
	d.lock.Lock()
	defer d.lock.Unlock()
	d.nodeID = nodeID
}

// setRsaKey sets handler.rsaKey
func (d *Dialer) setRsaKey(rsaReader RsaReader) error {
	d.lock.Lock()
	defer d.lock.Unlock()

	var err error
	d.rsaKey, err = rsaReader()

	return err
}

// SetContractCaller sets contract calling related fields in dialer
func (d *Dialer) SetContractCaller(contractCaller *ContractCaller) error {

	// creates an contract instance
	contractInstance, err := dpor.NewProposerRegister(d.contractAddress, contractCaller.Client)
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
	err = d.setRsaKey(rsaReader)
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
func (d *Dialer) UpdateRemoteProposers(term uint64, proposers []common.Address) error {

	for _, signer := range proposers {
		_, ok := d.getProposer(signer.Hex())
		if !ok {
			p := NewRemoteProposer(signer)
			d.setProposer(signer.Hex(), p)
		}
	}

	return nil
}

// UpdateRemoteValidators updates dialer.remoteValidators.
func (d *Dialer) UpdateRemoteValidators(term uint64, validators []common.Address) error {

	for _, signer := range validators {
		_, ok := d.getValidator(signer.Hex())
		if !ok {
			p := NewRemoteValidator(term, signer)
			d.setValidator(signer.Hex(), p)
		}
	}

	return nil
}

// DialAllRemoteProposers dials all remote proposers
func (d *Dialer) DialAllRemoteProposers(term uint64) error {

	d.lock.RLock()
	rsaKey, server := d.rsaKey, d.server
	validator := d.coinbase
	contractInstance := d.contractInstance
	d.lock.RUnlock()

	proposers := d.ProposersOfTerm(term)

	for _, p := range proposers {
		_, err := p.FetchNodeInfoAndDial(term, validator, server, rsaKey, contractInstance)
		if err != nil {
			return err
		}
	}

	return nil
}

// UploadEncryptedNodeInfo dials all remote validators
func (d *Dialer) UploadEncryptedNodeInfo(term uint64) error {

	d.lock.RLock()
	nodeID := d.nodeID
	contractInstance, contractTransactor, client := d.contractInstance, d.contractTransactor, d.contractCaller.Client
	d.lock.RUnlock()

	validators := d.ValidatorsOfTerm(term)

	for _, v := range validators {
		_, err := v.UploadNodeInfo(term, nodeID, contractTransactor, contractInstance, client)
		if err != nil {
			return err
		}
	}

	return nil
}

// Disconnect disconnects all proposers.
func (d *Dialer) Disconnect(term uint64) {
	d.lock.RLock()
	server := d.server
	d.lock.RUnlock()

	proposers := d.ProposersOfTerm(term)

	log.Debug("disconnecting...")

	for _, p := range proposers {
		err := p.disconnect(server)
		log.Debug("err when disconnect", "e", err)
	}
}

func (d *Dialer) getProposer(addr string) (*RemoteProposer, bool) {
	d.proposersLock.RLock()
	defer d.proposersLock.RUnlock()

	if rp, ok := d.recentProposers.Get(addr); ok {
		remoteProposer, ok := rp.(*RemoteProposer)
		return remoteProposer, ok
	}
	return nil, false
}

func (d *Dialer) setProposer(addr string, proposer *RemoteProposer) {
	d.proposersLock.Lock()
	defer d.proposersLock.Unlock()

	d.recentProposers.Add(addr, proposer)
}

func (d *Dialer) getValidator(addr string) (*RemoteValidator, bool) {
	d.validatorsLock.RLock()
	defer d.validatorsLock.RUnlock()

	if rp, ok := d.recentValidators.Get(addr); ok {
		remoteValidator, ok := rp.(*RemoteValidator)
		return remoteValidator, ok
	}
	return nil, false
}

func (d *Dialer) setValidator(addr string, validator *RemoteValidator) {
	d.validatorsLock.Lock()
	defer d.validatorsLock.Unlock()

	d.recentValidators.Add(addr, validator)
}

// ProposersOfTerm returns all proposers of given term
func (d *Dialer) ProposersOfTerm(term uint64) map[common.Address]*RemoteProposer {
	d.proposersLock.RLock()
	defer d.proposersLock.RUnlock()

	addrs := d.recentProposers.Keys()
	proposers := make(map[common.Address]*RemoteProposer)

	log.Debug("proposers in dialer", "count", len(addrs))

	for _, addr := range addrs {
		address := addr.(string)
		if ok, err := d.dpor.VerifyProposerOf(common.HexToAddress(address), term); ok && err == nil {
			proposer, _ := d.recentProposers.Get(addr)
			proposers[common.HexToAddress(address)] = proposer.(*RemoteProposer)
		}
	}

	return proposers
}

// ValidatorsOfTerm returns all validators of given term
func (d *Dialer) ValidatorsOfTerm(term uint64) map[common.Address]*RemoteValidator {
	// TODO: @AC @liuq the returned result include non-validator, will correct it
	d.validatorsLock.RLock()
	defer d.validatorsLock.RUnlock()

	addrs := d.recentValidators.Keys()
	validators := make(map[common.Address]*RemoteValidator)

	log.Debug("validators in dialer", "count", len(addrs))

	for _, addr := range addrs {
		address := addr.(string)
		if ok, err := d.dpor.VerifyValidatorOf(common.HexToAddress(address), term); ok && err == nil {
			validator, _ := d.recentValidators.Get(addr)
			validators[common.HexToAddress(address)] = validator.(*RemoteValidator)
		}
	}

	return validators
}
