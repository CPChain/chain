package dpor

import (
	"math/big"
	"time"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/log"
)

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
	hash := d.chain.CurrentHeader().Hash()
	number := d.chain.CurrentHeader().Number.Uint64()
	block := d.chain.GetBlock(hash, number)
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

	// TODO: fix this
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

	// TODO: fix this
	return false, nil
}

func (d *Dpor) ValidatorsOf(number uint64) ([]common.Address, error) {
	snap := d.currentSnap
	if snap == nil {
		log.Warn("currentSnap field is nil")
		return []common.Address{}, nil
	}

	term := snap.TermOf(number)
	return snap.getRecentValidators(term), nil
}

func (d *Dpor) ProposersOf(number uint64) ([]common.Address, error) {
	snap := d.currentSnap
	if snap == nil {
		log.Warn("currentSnap field is nil")
		return []common.Address{}, nil
	}

	term := snap.TermOf(number)
	return snap.getRecentProposers(term), nil
}

func (d *Dpor) ValidatorsOfTerm(term uint64) ([]common.Address, error) {
	snap := d.currentSnap
	if snap == nil {
		log.Warn("currentSnap field is nil")
		return []common.Address{}, nil
	}

	return snap.getRecentValidators(term), nil
}

func (d *Dpor) ProposersOfTerm(term uint64) ([]common.Address, error) {
	snap := d.currentSnap
	if snap == nil {
		log.Warn("currentSnap field is nil")
		return []common.Address{}, nil
	}

	return snap.getRecentProposers(term), nil
}

// VerifyHeaderWithState verifies the given header
// if in preprepared state, verify basic fields
// if in prepared state, verify if enough prepare sigs
// if in committed state, verify if enough commit sigs
func (d *Dpor) VerifyHeaderWithState(header *types.Header, state consensus.State) error {

	// TODO: fix this, !!! state
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
		Time:       new(big.Int).Add(parent.Time(), big.NewInt(int64(d.ImpeachTimeout()/time.Millisecond)+int64(d.config.Period))),
		Coinbase:   common.Address{},
		StateRoot:  parentHeader.StateRoot,
	}

	impeach := types.NewBlock(impeachHeader, []*types.Transaction{}, []*types.Receipt{})

	return impeach, nil
}

// ECRecoverSigs recovers signer address and corresponding signature, it ignores empty signature and return empty
// addresses if one of the sigs are illegal
// TODO: refactor this, return a map[common.Address]dpor.Signature
func (d *Dpor) ECRecoverSigs(header *types.Header, state consensus.State) ([]common.Address, []types.DporSignature, error) {

	// get hash with state
	hashToSign, err := HashBytesWithState(d.dh.sigHash(header).Bytes(), state)
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

// Update the signature to prepare signature cache(two kinds of sigs, one for prepared, another for final)
func (d *Dpor) UpdatePrepareSigsCache(validator common.Address, hash common.Hash, sig types.DporSignature) {
	s, ok := d.prepareSigs.Get(hash)
	if !ok {
		s = &Signatures{
			sigs: make(map[common.Address][]byte),
		}
		d.prepareSigs.Add(hash, s)
	}
	s.(*Signatures).SetSig(validator, sig[:])
}

// Update the signature to final signature cache(two kinds of sigs, one for prepared, another for final)
func (d *Dpor) UpdateFinalSigsCache(validator common.Address, hash common.Hash, sig types.DporSignature) {
	s, ok := d.finalSigs.Get(hash)
	if !ok {
		s = &Signatures{
			sigs: make(map[common.Address][]byte),
		}
		d.finalSigs.Add(hash, s)
	}
	s.(*Signatures).SetSig(validator, sig[:])
}

// GetMac signs a Mac
func (d *Dpor) GetMac() (mac string, sig []byte, err error) {
	prefix := "cpchain"
	t := time.Now().Format(time.RFC3339)
	split := "|"
	mac = prefix + split + t

	var hash common.Hash
	hasher := sha3.NewKeccak256()
	hasher.Write([]byte(mac))
	hasher.Sum(hash[:0])

	log.Debug("generated mac", "mac", mac)

	sig, err = d.signFn(accounts.Account{Address: d.Coinbase()}, hash.Bytes())
	return mac, sig, err
}
