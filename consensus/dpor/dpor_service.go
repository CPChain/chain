package dpor

import (
	"math/big"
	"time"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/p2p"
)

// Those are functions implement backend.DporService

// Period returns period of block generation
func (d *Dpor) Period() time.Duration {
	return d.config.PeriodDuration()
}

// TermLength returns term length
func (d *Dpor) TermLength() uint64 {
	return d.config.TermLen
}

// Faulty returns the number of faulty nodes
func (d *Dpor) Faulty() uint64 {
	return d.config.FaultyNumber
}

// BlockDelay returns max delay of preprepare block propagation
func (d *Dpor) BlockDelay() time.Duration {
	return d.config.BlockDelay()
}

// ViewLength returns view length
func (d *Dpor) ViewLength() uint64 {
	return d.config.ViewLen
}

// ValidatorsNum returns number of validators
func (d *Dpor) ValidatorsNum() uint64 {
	return d.config.ValidatorsLen()
}

// TermOf returns the term number of given block number
func (d *Dpor) TermOf(number uint64) uint64 {
	if d.currentSnap == nil {
		log.Warn("currentSnap field is nil")
		return 0
	}

	return d.currentSnap.TermOf(number)
}

// FutureTermOf returns the future term number of given block number
func (d *Dpor) FutureTermOf(number uint64) uint64 {
	if d.currentSnap == nil {
		log.Warn("currentSnap field is nil")
		return 0
	}

	return d.currentSnap.FutureTermOf(number)
}

// GetCurrentBlock returns current block
func (d *Dpor) GetCurrentBlock() *types.Block {
	block := d.chain.CurrentBlock()
	return block
}

// VerifyProposerOf verifies if an address is a proposer of given term
func (d *Dpor) VerifyProposerOf(signer common.Address, term uint64) (bool, error) {
	snap := d.currentSnap
	if snap == nil {
		log.Warn("currentSnap field is nil")
		return false, nil
	}

	proposers := snap.getRecentProposers(term)

	log.Debug("proposers in dpor current snapshot", "count", len(proposers), "term", term)

	for _, p := range proposers {
		if p == signer {
			return true, nil
		}
	}

	return false, nil
}

// VerifyValidatorOf verifies if an address is a validator of given term
func (d *Dpor) VerifyValidatorOf(signer common.Address, term uint64) (bool, error) {
	snap := d.currentSnap
	if snap == nil {
		log.Warn("currentSnap field is nil")
		return false, nil
	}

	validators := snap.getRecentValidators(term)

	log.Debug("validators in dpor current snapshot", "count", len(validators), "term", term)

	for _, p := range validators {
		if p == signer {
			return true, nil
		}
	}

	return false, nil
}

// ValidatorsOf returns validators of given block number
func (d *Dpor) ValidatorsOf(number uint64) ([]common.Address, error) {
	snap := d.currentSnap
	if snap == nil {
		log.Warn("currentSnap field is nil")
		return []common.Address{}, nil
	}

	term := snap.TermOf(number)
	return snap.getRecentValidators(term), nil
}

// ProposersOf returns proposers of given block number
func (d *Dpor) ProposersOf(number uint64) ([]common.Address, error) {
	snap := d.currentSnap
	if snap == nil {
		log.Warn("currentSnap field is nil")
		return []common.Address{}, nil
	}

	term := snap.TermOf(number)
	return snap.getRecentProposers(term), nil
}

// ProposerOf returns the proposer of the specified block number by rpt and election calculation
func (d *Dpor) ProposerOf(number uint64) (common.Address, error) {
	snap := d.currentSnap
	if snap == nil {
		log.Warn("currentSnap field is nil")
		return common.Address{}, nil
	}

	proposers, _ := d.ProposersOf(number)
	for _, p := range proposers {
		if ok, err := snap.IsProposerOf(p, number); ok && err == nil {
			return p, nil
		}
	}

	return common.Address{}, nil
}

// IsProposerOf returns whether the given address is the proposer for the block number
func (d *Dpor) IsProposerOf(addr common.Address, number uint64) (bool, error) {
	p, err := d.ProposerOf(number)
	return p == addr, err
}

// ValidatorsOfTerm returns validators of given term
// TODO: this only returns validators known recently from cache,
// does not retrieve block from local chain to get needed information.
// maybe i'll add it later.
func (d *Dpor) ValidatorsOfTerm(term uint64) ([]common.Address, error) {
	snap := d.currentSnap
	if snap == nil {
		log.Warn("currentSnap field is nil")
		return []common.Address{}, nil
	}

	return snap.getRecentValidators(term), nil
}

// ProposersOfTerm returns proposers of given term
// TODO: same as above
func (d *Dpor) ProposersOfTerm(term uint64) ([]common.Address, error) {
	snap := d.currentSnap
	if snap == nil {
		log.Warn("currentSnap field is nil")
		return []common.Address{}, nil
	}

	return snap.getRecentProposers(term), nil
}

// VerifyHeaderWithState verifies the given header
// TODO: review this!
func (d *Dpor) VerifyHeaderWithState(header *types.Header, state consensus.State) error {
	return d.VerifyHeader(d.chain, header, true, header)
}

// ValidateBlock validates a basic field excepts seal of a block.
func (d *Dpor) ValidateBlock(block *types.Block, verifySigs bool, verifyProposers bool) error {
	return d.dh.validateBlock(d, d.chain, block, verifySigs, verifyProposers)
}

// SignHeader signs the header and adds all known sigs to header
func (d *Dpor) SignHeader(header *types.Header, state consensus.State) error {
	switch err := d.dh.signHeader(d, d.chain, header, state); err {
	case nil:
		return nil
	default:
		return err
	}
}

// BroadcastBlock broadcasts a block to normal peers(not pbft replicas)
func (d *Dpor) BroadcastBlock(block *types.Block, prop bool) {
	go d.pmBroadcastBlockFn(block, prop)
}

// InsertChain inserts a block to chain
func (d *Dpor) InsertChain(block *types.Block) error {
	_, err := d.chain.InsertChain(types.Blocks{block})
	return err
}

// Status returns a pbft replica's status
func (d *Dpor) Status() *consensus.PbftStatus {
	return d.PbftStatus()
}

// StatusUpdate updates status of dpor
func (d *Dpor) StatusUpdate() error {

	// TODO: fix this
	return nil
}

// HasBlockInChain returns if a block is in local chain
func (d *Dpor) HasBlockInChain(hash common.Hash, number uint64) bool {
	blk := d.chain.GetBlock(hash, number)
	if blk != nil {
		return true
	}
	return false
}

// GetBlockFromChain implements DporService.GetBlockFromChain
func (d *Dpor) GetBlockFromChain(hash common.Hash, number uint64) *types.Block {
	return d.chain.GetBlock(hash, number)
}

// CreateImpeachBlock creates an impeachment block
func (d *Dpor) CreateImpeachBlock() (*types.Block, error) {
	parentHeader := d.chain.CurrentHeader()
	parentNum := parentHeader.Number.Uint64()

	parent := d.chain.GetBlock(parentHeader.Hash(), parentNum)

	impeachHeader := &types.Header{
		ParentHash: parent.Hash(),
		Number:     big.NewInt(int64(parentNum + 1)),
		GasLimit:   parent.GasLimit(),
		Extra:      make([]byte, extraSeal),
		Coinbase:   common.Address{},
		StateRoot:  parentHeader.StateRoot,
	}

	for _, proposer := range d.CurrentSnap().ProposersOf(parentNum + 1) {
		impeachHeader.Dpor.Proposers = append(impeachHeader.Dpor.Proposers, proposer)
	}
	impeachHeader.Dpor.Sigs = make([]types.DporSignature, d.config.ValidatorsLen())

	timestamp := parent.Timestamp().Add(d.config.PeriodDuration()).Add(d.config.ImpeachTimeout)
	impeachHeader.SetTimestamp(timestamp)

	impeach := types.NewBlock(impeachHeader, []*types.Transaction{}, []*types.Receipt{})

	return impeach, nil
}

// CreateImpeachBlockAt creates an impeachment block
func (d *Dpor) CreateImpeachBlockAt(parentHeader *types.Header) (*types.Block, error) {
	parentNum := parentHeader.Number.Uint64()
	parent := d.chain.GetBlock(parentHeader.Hash(), parentNum)

	impeachHeader := &types.Header{
		ParentHash: parent.Hash(),
		Number:     big.NewInt(int64(parentNum + 1)),
		GasLimit:   parent.GasLimit(),
		Extra:      make([]byte, extraSeal),
		Coinbase:   common.Address{},
		StateRoot:  parentHeader.StateRoot,
	}

	for _, proposer := range d.CurrentSnap().ProposersOf(parentNum + 1) {
		impeachHeader.Dpor.Proposers = append(impeachHeader.Dpor.Proposers, proposer)
	}
	impeachHeader.Dpor.Sigs = make([]types.DporSignature, d.config.ValidatorsLen())

	timestamp := parent.Timestamp().Add(d.config.PeriodDuration()).Add(d.config.ImpeachTimeout)
	impeachHeader.SetTimestamp(timestamp)

	impeach := types.NewBlock(impeachHeader, []*types.Transaction{}, []*types.Receipt{})

	return impeach, nil
}

// CreateFailbackImpeachBlocks creates impeachment blocks with failback timestamps
func (d *Dpor) CreateFailbackImpeachBlocks() (firstImpeachment *types.Block, secondImpeachment *types.Block, err error) {

	impeachBlock, err := d.CreateImpeachBlock()
	if err != nil {
		return nil, nil, err
	}

	failbackTimestamp1 := (time.Now().UnixNano()/int64(configs.DefaultFailbackTimestampSampleSpace) + 1) * int64(configs.DefaultFailbackTimestampSampleSpace)
	failbackTimestamp2 := failbackTimestamp1 + int64(configs.DefaultFailbackTimestampSampleSpace)

	firstImpeachment = types.NewBlock(impeachBlock.Header(), []*types.Transaction{}, []*types.Receipt{})
	firstImpeachment.RefHeader().SetTimestamp(time.Unix(0, failbackTimestamp1))

	secondImpeachment = types.NewBlock(impeachBlock.Header(), []*types.Transaction{}, []*types.Receipt{})
	secondImpeachment.RefHeader().SetTimestamp(time.Unix(0, failbackTimestamp2))

	return
}

// ECRecoverSigs recovers signer address and corresponding signature, it ignores empty signature and return empty
// addresses if one of the sigs are illegal
// TODO: refactor this, return a map[common.Address]dpor.Signature
func (d *Dpor) ECRecoverSigs(header *types.Header, state consensus.State) ([]common.Address, []types.DporSignature, error) {

	// get hash with state
	hashToSign, err := hashBytesWithState(d.dh.sigHash(header).Bytes(), state)
	if err != nil {
		log.Warn("failed to get hash bytes with state", "number", header.Number.Uint64(), "hash", header.Hash().Hex(), "state", state)
		return nil, nil, err
	}

	sigs := header.Dpor.Sigs
	validators := make([]common.Address, 0, len(sigs))
	validatorSignatures := make([]types.DporSignature, 0, len(sigs))
	for _, sig := range sigs {
		if !sig.IsEmpty() {

			validatorPubKey, err := crypto.Ecrecover(hashToSign, sig[:])
			if err != nil {
				return []common.Address{}, []types.DporSignature{}, err
			}

			addr := common.Address{}
			copy(addr[:], crypto.Keccak256(validatorPubKey[1:])[12:])
			validators = append(validators, addr)
			validatorSignatures = append(validatorSignatures, sig)
		}
	}
	return validators, validatorSignatures, nil
}

// ECRecoverProposer recovers a proposer address from the seal of given header
func (d *Dpor) ECRecoverProposer(header *types.Header) (common.Address, error) {
	var proposer common.Address
	proposerSig := header.Dpor.Seal

	proposerPubKey, err := crypto.Ecrecover(d.dh.sigHash(header).Bytes(), proposerSig[:])
	if err != nil {
		return common.Address{}, err
	}

	copy(proposer[:], crypto.Keccak256(proposerPubKey[1:])[12:])
	return proposer, nil
}

// UpdatePrepareSigsCache updates prepare signature of a validator for a block in cache
func (d *Dpor) UpdatePrepareSigsCache(validator common.Address, hash common.Hash, sig types.DporSignature) {
	s, ok := d.prepareSigs.Get(hash)
	if !ok {
		s = &signatures{
			sigs: make(map[common.Address][]byte),
		}
		d.prepareSigs.Add(hash, s)
	}
	s.(*signatures).setSig(validator, sig[:])
}

// UpdateFinalSigsCache updates final(commit) signature of a validator for a block in cache
func (d *Dpor) UpdateFinalSigsCache(validator common.Address, hash common.Hash, sig types.DporSignature) {
	s, ok := d.finalSigs.Get(hash)
	if !ok {
		s = &signatures{
			sigs: make(map[common.Address][]byte),
		}
		d.finalSigs.Add(hash, s)
	}
	s.(*signatures).setSig(validator, sig[:])
}

// GetMac composes a message authentication code and signs it
func (d *Dpor) GetMac() (mac string, sig []byte, err error) {

	// mac is like this: "cpchain|2019-02-26T16:22:21+08:00"

	// compose the msg
	prefix := "cpchain"
	t := time.Now().Format(time.RFC3339)
	split := "|"
	mac = prefix + split + t

	// make a hash for it
	var hash common.Hash
	hasher := sha3.NewKeccak256()
	hasher.Write([]byte(mac))
	hasher.Sum(hash[:0])

	log.Debug("generated mac", "mac", mac)

	// sign it!
	sig, err = d.signFn(accounts.Account{Address: d.Coinbase()}, hash.Bytes())

	return mac, sig, err
}

// SyncFrom tries to sync blocks from given peer
func (d *Dpor) SyncFrom(p *p2p.Peer) {
	go d.pmSyncFromPeerFn(p)
}

// Synchronize tries to sync blocks from best peer
func (d *Dpor) Synchronize() {
	go d.pmSyncFromBestPeerFn()
}

// IsDefaultProposer returns if the given address is a default proposer
func (d *Dpor) IsDefaultProposer(address common.Address) bool {
	for _, addr := range configs.Proposers() {
		if addr == address {
			return true
		}
	}
	return false
}

// IsCurrentOrFutureProposer checks if an address is a proposer in the period between current term and future term
func (d *Dpor) IsCurrentOrFutureProposer(address common.Address) bool {
	if d.Mode() != NormalMode {
		return true
	}

	snap := d.CurrentSnap()
	number := snap.number()
	term := snap.TermOf(number)
	futureTerm := snap.FutureTermOf(number)

	isProposer := false
	for t := term; t <= futureTerm; t++ {
		isP, _ := d.VerifyProposerOf(address, t)
		isProposer = isProposer || isP
	}
	return isProposer
}

func (d *Dpor) PeerInfos() ([]*backend.PeerInfo, error) {
	if d.handler != nil {
		return d.handler.PeerInfos()
	}
	return nil, errDporProtocolNotWorking
}
