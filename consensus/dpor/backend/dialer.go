package backend

import (
	"fmt"
	"strings"
	"sync"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
	lru "github.com/hashicorp/golang-lru"
)

const (
	maxNumOfRemoteSignersInCache = 10
)

// Dialer dials a remote peer
type Dialer struct {
	server *p2p.Server
	lock   sync.RWMutex

	dpor DporService

	// use lru caches to cache recent proposers and validators
	recentProposers *lru.ARCCache
	proposersLock   sync.RWMutex // to protect recent proposers

	recentValidators *lru.ARCCache
	validatorsLock   sync.RWMutex // to protect recent validators

	defaultValidators []string
}

// NewDialer creates a new dialer to dial remote peers
func NewDialer() *Dialer {

	proposers, _ := lru.NewARC(maxNumOfRemoteSignersInCache)
	validators, _ := lru.NewARC(maxNumOfRemoteSignersInCache)

	return &Dialer{
		recentProposers:   proposers,
		recentValidators:  validators,
		defaultValidators: configs.GetDefaultValidators(),
	}
}

// SetDporService sets dpor service to dialer
func (d *Dialer) SetDporService(dpor DporService) {
	d.dpor = dpor
}

// AddPeer adds a peer to local dpor peer set:
// remote proposers or remote validators
func (d *Dialer) AddPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter, mac string, sig []byte, term uint64, futureTerm uint64) (string, bool, bool, error) {
	address, isProposer, isValidator, err := d.addPeer(version, p, rw, mac, sig, term, futureTerm)
	return address, isProposer, isValidator, err
}

func (d *Dialer) addPeer(version int, p *p2p.Peer, rw p2p.MsgReadWriter, mac string, sig []byte, term uint64, futureTerm uint64) (string, bool, bool, error) {
	log.Debug("do handshaking with remote peer...")

	address, err := Handshake(p, rw, mac, sig, term, futureTerm)

	log.Debug("received handshake from", "addr", address.Hex())

	// TODO: fix this @liuq
	isProposer, isValidator := true, false
	// isProposer, isValidator := false, false

	for t := term; t <= futureTerm; t++ {
		isP, _ := d.dpor.VerifyProposerOf(address, t)
		// isV, _ := d.dpor.VerifyValidatorOf(address, t)

		// log.Debug("qualification", "is proposer", isP, "is validator", isV, "term", t, "addr", address.Hex())

		isProposer = isProposer || isP
		// isValidator = isValidator || isV
	}

	enode := fmt.Sprintf("enode://%s@%s", p.ID().String(), p.RemoteAddr().String())
	isValidator = isDefaultValidator(enode, d.defaultValidators)

	log.Debug("qualification", "is proposer", isProposer, "is validator", isValidator, "addr", address.Hex(), "enode", enode)

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

// DialAllRemoteValidators tries to dial all remote validators
func (d *Dialer) DialAllRemoteValidators(term uint64) error {
	for _, validatorID := range d.defaultValidators {
		node, err := discover.ParseNode(validatorID)
		if err != nil {
			continue
		}
		log.Debug("dial remote validator", "enode", node.ID.String(), "addr", node.IP.String(), "port", node.TCP)
		d.server.AddPeer(node)
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
		proposer, _ := d.recentProposers.Get(addr)
		proposers[common.HexToAddress(address)] = proposer.(*RemoteProposer)
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

		if d.dpor != nil {
			ok, err := d.dpor.VerifyValidatorOf(common.HexToAddress(address), term)

			v, _ := d.recentValidators.Get(addr)
			validator := v.(*RemoteValidator)

			if isDefaultValidator(validator.EnodeID(), d.defaultValidators) || (ok && err == nil) {
				validators[common.HexToAddress(address)] = validator
			}
		}
	}

	return validators
}

// isDefaultValidator checks if a validator is a default validator
func isDefaultValidator(enode string, defaultValidators []string) bool {
	for _, dv := range defaultValidators {
		if enodeIDWithoutPort(dv) == enodeIDWithoutPort(enode) {
			return true
		}
	}
	return false
}

func enodeIDWithoutPort(enode string) string {
	s := strings.Split(enode, ":")
	return strings.Join(s[:len(s)-1], ":")
}
