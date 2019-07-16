package backend

import (
	"strings"
	"sync"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
	lru "github.com/hashicorp/golang-lru"
)

const (
	maxNumOfRemoteSignersInCache = 200
)

// Dialer dials a remote peer
type Dialer struct {
	server *p2p.Server
	lock   sync.RWMutex

	dpor DporService

	// use lru caches to cache recent proposers and validators
	recentProposers  *lru.ARCCache
	recentValidators *lru.ARCCache

	defaultValidators []string

	quitCh chan struct{}
}

// NewDialer creates a new dialer to dial remote peers
func NewDialer() *Dialer {

	proposers, _ := lru.NewARC(maxNumOfRemoteSignersInCache)
	validators, _ := lru.NewARC(maxNumOfRemoteSignersInCache)

	return &Dialer{
		recentProposers:   proposers,
		recentValidators:  validators,
		quitCh:            make(chan struct{}),
		defaultValidators: configs.GetDefaultValidators(),
	}
}

// SetDporService sets dpor service to dialer
func (d *Dialer) SetDporService(dpor DporService) {
	d.dpor = dpor
}

// AddPeer adds a peer to local dpor peer set:
// remote proposers or remote validators
func (d *Dialer) AddPeer(cpcVersion int, p *p2p.Peer, rw p2p.MsgReadWriter, mac string, sig []byte, term uint64, futureTerm uint64) (string, bool, bool, error) {
	address, isProposer, isValidator, err := d.addPeer(cpcVersion, p, rw, mac, sig, term, futureTerm)
	return address, isProposer, isValidator, err
}

// isCurrentOrFutureProposer checks if an address is a proposer in the period between current term and future term
func (d *Dialer) isCurrentOrFutureProposer(address common.Address, term uint64, futureTerm uint64) bool {
	isProposer := false
	for t := term; t <= futureTerm; t++ {
		isP, _ := d.dpor.VerifyProposerOf(address, t)
		log.Debug("qualification", "is proposer", isP, "term", t, "addr", address.Hex())
		isProposer = isProposer || isP
	}
	return isProposer
}

// isCurrentOrFutureValidator checks if an address is a validator in the period between current term and future term
func (d *Dialer) isCurrentOrFutureValidator(address common.Address, term uint64, futureTerm uint64) bool {
	isValidator := false
	for t := term; t <= futureTerm; t++ {
		isV, _ := d.dpor.VerifyValidatorOf(address, t)
		log.Debug("qualification", "is validator", isV, "term", t, "addr", address.Hex())
		isValidator = isValidator || isV
	}
	return isValidator
}

// addPeer tries to add a p2p peer as a proposer or a validator to local peer set based on its coinbase
func (d *Dialer) addPeer(cpcVersion int, p *p2p.Peer, rw p2p.MsgReadWriter, mac string, sig []byte, term uint64, futureTerm uint64) (string, bool, bool, error) {

	// handshake to get remote peer's coinbase
	log.Debug("do handshaking with remote peer...")
	coinbase, dporVersion, err := Handshake(p, rw, mac, sig, term, futureTerm)

	// some debug output
	log.Debug("received handshake from", "addr", coinbase.Hex())

	// check whether or not remote peer is a proposer or a validator in the period between current term and future term
	isProposer, isValidator := d.isCurrentOrFutureProposer(coinbase, term, futureTerm), d.isCurrentOrFutureValidator(coinbase, term, futureTerm)

	// also check if remote peer is a validator
	isValidator = IsDefaultValidator(p.ID().String(), d.defaultValidators) || isValidator

	// debug output
	log.Debug("qualification", "is proposer", isProposer, "is validator", isValidator, "addr", coinbase.Hex())

	// if remote peer is neither a proposer nor a validator, disconnect it
	if (!isProposer && !isValidator) || err != nil {
		log.Debug("failed to handshake in dpor", "err", err, "isProposer", isProposer, "isValidator", isValidator)
		return "", isProposer, isValidator, err
	}

	// if the remote peer is a proposer, add it to local peer set
	if isProposer {
		remoteProposer, err := d.addRemoteProposer(cpcVersion, dporVersion, p, rw, coinbase)
		log.Debug("after add remote proposer", "proposer", remoteProposer.ID(), "err", err)
	}

	// if the remote peer is a validator, add it to local peer set
	if isValidator {
		remoteValidator, err := d.addRemoteValidator(cpcVersion, dporVersion, p, rw, coinbase)
		log.Debug("after add remote validator", "validator", remoteValidator.ID(), "err", err)
	}

	return coinbase.Hex(), isProposer, isValidator, err
}

// addRemoteProposer adds a p2p peer to local proposers set
func (d *Dialer) addRemoteProposer(cpcVersion int, dporVersion int, p *p2p.Peer, rw p2p.MsgReadWriter, address common.Address) (*RemoteProposer, error) {
	remoteProposer, ok := d.getProposer(address.Hex())
	if !ok {
		remoteProposer = NewRemoteProposer(address)
	}

	log.Debug("adding remote proposer...", "proposer", address.Hex())

	// add proposer
	remoteProposer.SetPeer(cpcVersion, dporVersion, Proposer, p, rw)
	d.setProposer(address.Hex(), remoteProposer)

	return remoteProposer, nil
}

// addRemoteValidator adds a p2p peer to local validators set
func (d *Dialer) addRemoteValidator(cpcVersion int, dporVersion int, p *p2p.Peer, rw p2p.MsgReadWriter, address common.Address) (*RemoteValidator, error) {
	remoteValidator, ok := d.getValidator(address.Hex())
	if !ok {
		remoteValidator = NewRemoteValidator(address)
	}

	log.Debug("adding remote validator...", "validator", address.Hex())

	// add validator
	remoteValidator.SetPeer(cpcVersion, dporVersion, Validator, p, rw)
	d.setValidator(address.Hex(), remoteValidator)

	// start broadcast loop
	go remoteValidator.broadcastLoop()

	return remoteValidator, nil
}

// removeRemoteProposers removes remote proposer by it's addr
func (d *Dialer) removeRemoteProposers(addr string) error {
	d.recentProposers.Remove(addr)
	return nil
}

// removeRemoteValidators removes remote proposer by it's addr
func (d *Dialer) removeRemoteValidators(addr string) error {
	v, ok := d.recentValidators.Get(addr)
	if ok {
		validator, ok := v.(*RemoteValidator)
		if ok {
			validator.Stop()
		}
		d.recentValidators.Remove(addr)
	}
	return nil
}

// SetServer sets dialer.server
func (d *Dialer) SetServer(server *p2p.Server) {
	d.lock.Lock()
	defer d.lock.Unlock()

	d.server = server
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

// dialAllRemoteValidators tries to dial all remote validators
func (d *Dialer) dialAllRemoteValidators(term uint64) {

	validators := d.ValidatorsOfTerm(term)

	// dial validators not connected yet
	for _, validatorID := range d.defaultValidators {
		node, err := discover.ParseNode(validatorID)
		if err != nil {
			continue
		}

		connected := false
		for _, v := range validators {
			if node.ID == v.ID() {
				connected = true
			}
		}

		if !connected {
			log.Debug("dial remote validator", "enode", node.ID.String(), "addr", node.IP.String(), "port", node.TCP)
			d.server.AddPeer(node)
		}
	}
}

// disconnectValidators disconnects all Validators.
func (d *Dialer) disconnectValidators(term uint64) {

	log.Debug("disconnecting validators of term...", "term", term)

	server := d.server
	validators := d.ValidatorsOfTerm(term)

	for _, p := range validators {
		err := p.disconnect(server)
		if err != nil {
			log.Debug("err when disconnect", "e", err)
		}
	}
}

// disconnectProposers disconnects all proposers of the given term.
func (d *Dialer) disconnectProposers(term uint64) {

	log.Debug("disconnecting proposers of term...", "term", term)

	server := d.server
	proposers := d.ProposersOfTerm(term)

	for _, p := range proposers {
		err := p.disconnect(server)
		if err != nil {
			log.Debug("err when disconnect", "e", err)
		}
	}
}

// disconnectUselessProposers disconnects all useless proposers.
func (d *Dialer) disconnectUselessProposers() {

	log.Debug("disconnecting all useless proposers...")

	server := d.server
	proposers := d.AllUselessProposers()

	for _, p := range proposers {
		err := p.disconnect(server)
		if err != nil {
			log.Debug("err when disconnect", "e", err)
		}
	}
}

func (d *Dialer) getProposer(addr string) (*RemoteProposer, bool) {
	if rp, ok := d.recentProposers.Get(addr); ok {
		remoteProposer, ok := rp.(*RemoteProposer)
		return remoteProposer, ok
	}
	return nil, false
}

func (d *Dialer) setProposer(addr string, proposer *RemoteProposer) {
	d.recentProposers.Add(addr, proposer)
}

func (d *Dialer) getValidator(addr string) (*RemoteValidator, bool) {
	if rv, ok := d.recentValidators.Get(addr); ok {
		remoteValidator, ok := rv.(*RemoteValidator)
		return remoteValidator, ok
	}
	return nil, false
}

func (d *Dialer) setValidator(addr string, validator *RemoteValidator) {
	d.recentValidators.Add(addr, validator)
}

// AllUselessProposers returns all useless proposers
func (d *Dialer) AllUselessProposers() map[common.Address]*RemoteProposer {
	// get all proposers
	addrs := d.recentProposers.Keys()
	proposers := make(map[common.Address]*RemoteProposer)

	log.Debug("proposers in dialer", "count", len(addrs))

	for _, addr := range addrs {
		address, useful := common.HexToAddress(addr.(string)), false
		proposer, ok := d.recentProposers.Get(addr)

		if currentBlock := d.dpor.GetCurrentBlock(); currentBlock != nil {
			var (
				currentNumber = currentBlock.NumberU64()
				currentTerm   = d.dpor.TermOf(currentNumber)
				futureTerm    = d.dpor.FutureTermOf(currentNumber)
			)
			useful = d.isCurrentOrFutureProposer(address, currentTerm, futureTerm)
		}

		if ok && !useful {
			proposers[address] = proposer.(*RemoteProposer)
		}
	}

	return proposers
}

// ProposersOfTerm returns all proposers of given term
func (d *Dialer) ProposersOfTerm(term uint64) map[common.Address]*RemoteProposer {
	// get all proposers
	addrs := d.recentProposers.Keys()
	proposers := make(map[common.Address]*RemoteProposer)

	log.Debug("proposers in dialer", "count", len(addrs))

	for _, addr := range addrs {
		address := common.HexToAddress(addr.(string))
		proposer, ok := d.recentProposers.Get(addr)
		isProposerOfTerm, err := d.dpor.VerifyProposerOf(address, term)

		// if it is a proposer of given term, return it
		if ok && isProposerOfTerm && err == nil {
			proposers[address] = proposer.(*RemoteProposer)
		}
	}

	return proposers
}

// ValidatorsOfTerm returns all validators of given term
func (d *Dialer) ValidatorsOfTerm(term uint64) map[common.Address]*RemoteValidator {
	addrs := d.recentValidators.Keys()
	validators := make(map[common.Address]*RemoteValidator)

	log.Debug("validators in dialer", "count", len(addrs))

	for _, addr := range addrs {
		address := common.HexToAddress(addr.(string))
		validator, ok := d.recentValidators.Get(addr)
		if !ok {
			continue
		}

		isValidatorOfTerm, err := d.dpor.VerifyValidatorOf(address, term)
		isDefaultV := IsDefaultValidator(validator.(*RemoteValidator).RemoteSigner.Peer.ID().String(), d.defaultValidators)

		// if the validator in peer set is a validator for given term or a default validator, return it
		if (isValidatorOfTerm && err == nil) || isDefaultV {
			validators[address] = validator.(*RemoteValidator)
		}

	}

	return validators
}

// IsDefaultValidator checks if a validator is a default validator
func IsDefaultValidator(nodeID string, defaultValidators []string) bool {
	for _, dv := range defaultValidators {
		node, _ := discover.ParseNode(dv)
		if node.ID.String() == nodeID {
			return true
		}
	}
	return false
}

func enodeIDWithoutPort(enode string) string {
	s := strings.Split(enode, ":")
	return strings.Join(s[:len(s)-1], ":")
}

// KeepConnection tries to dial remote validators if local node is a current or future proposer
// and disconnect remote validators if it is not
func (d *Dialer) KeepConnection() {
	futureTimer := time.NewTicker(d.dpor.Period() / 2)
	defer futureTimer.Stop()
	for {
		select {
		case <-futureTimer.C:
			if current := d.dpor.GetCurrentBlock(); current != nil {
				var (
					currentNum  = current.NumberU64()
					currentTerm = d.dpor.TermOf(currentNum)
					futureTerm  = d.dpor.FutureTermOf(currentNum)
					address     = d.dpor.Coinbase()
				)

				switch {
				case d.isCurrentOrFutureValidator(address, currentTerm, futureTerm):

					log.Debug("I am current or future validator, dialing remote validators and disconnecting useless proposers", "addr", address.Hex(), "number", currentNum, "term", currentTerm, "future term", futureTerm)

					d.dialAllRemoteValidators(currentTerm)
					d.disconnectUselessProposers()

				case d.isCurrentOrFutureProposer(address, currentTerm, futureTerm):

					log.Debug("I am current or future proposer, dialing remote validators", "addr", address.Hex(), "number", currentNum, "term", currentTerm, "future term", futureTerm)

					d.dialAllRemoteValidators(currentTerm)

				default:
					log.Debug("I am not a current or future proposer nor a validator, disconnecting remote validators", "addr", address.Hex(), "number", currentNum, "term", currentTerm, "future term", futureTerm)
					d.disconnectValidators(currentTerm)
				}
			}

		case <-d.quitCh:
			return
		}
	}
}

// EnoughValidatorsOfTerm returns validator of given term and whether it is enough
func (d *Dialer) EnoughValidatorsOfTerm(term uint64) (validators map[common.Address]*RemoteValidator, enough bool) {
	validators = d.ValidatorsOfTerm(term)
	enough = len(validators) >= int(d.dpor.Faulty()*2)
	return
}

// EnoughImpeachValidatorsOfTerm returns validator of given term and whether it is enough for impeach
func (d *Dialer) EnoughImpeachValidatorsOfTerm(term uint64) (validators map[common.Address]*RemoteValidator, enough bool) {
	validators = d.ValidatorsOfTerm(term)
	enough = len(validators) >= int(d.dpor.Faulty())
	return
}

func (d *Dialer) Stop() {
	d.disconnectValidators(0)
	close(d.quitCh)
	d.quitCh = make(chan struct{})

	return
}

func (d *Dialer) PeerInfos() ([]*PeerInfo, error) {
	var infos []*PeerInfo
	for _, id := range d.recentProposers.Keys() {
		proposer, ok := d.getProposer(id.(string))
		if ok {
			info := proposer.Info()
			if info != nil {
				infos = append(infos, info)
			}
		}
	}
	for _, id := range d.recentValidators.Keys() {
		validator, ok := d.getValidator(id.(string))
		if ok {
			info := validator.Info()
			if info != nil {
				infos = append(infos, info)
			}
		}
	}
	return infos, nil
}
