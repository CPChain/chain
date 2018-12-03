package dpor

import (
	"math/big"

	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

// TermOf returns the term number of given block number
func (d *Dpor) TermOf(number uint64) uint64 {
	return d.currentSnapshot.TermOf(number)
}

// FutureTermOf returns the future term number of given block number
func (d *Dpor) FutureTermOf(number uint64) uint64 {
	return d.currentSnapshot.FutureTermOf(number)
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

	// TODO: remove this
	if term <= 6 {
		return true, nil
	}
	snap := d.currentSnapshot
	proposers := snap.getRecentProposers(term)

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

	// TODO: remove this
	if term <= 6 {
		return true, nil
	}
	snap := d.currentSnapshot
	validators := snap.getRecentValidators(term)

	for _, p := range validators {
		if p == signer {
			return true, nil
		}
	}

	// TODO: fix this
	return false, nil
}

func (d *Dpor) ValidatorsOf(number uint64) ([]common.Address, error) {
	snap := d.currentSnapshot
	term := snap.TermOf(number)
	return snap.getRecentValidators(term), nil
}

func (d *Dpor) ProposersOf(number uint64) ([]common.Address, error) {
	snap := d.currentSnapshot
	term := snap.TermOf(number)
	return snap.getRecentProposers(term), nil
}

func (d *Dpor) ValidatorsOfTerm(term uint64) ([]common.Address, error) {
	snap := d.currentSnapshot
	return snap.getRecentValidators(term), nil
}

func (d *Dpor) ProposersOfTerm(term uint64) ([]common.Address, error) {
	snap := d.currentSnapshot
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
func (d *Dpor) ValidateBlock(block *types.Block) error {
	return d.dh.validateBlock(d, d.chain, block)
}

// SignHeader signs the header and adds all known sigs to header
func (d *Dpor) SignHeader(header *types.Header, state consensus.State) error {
	switch err := d.dh.signHeader(d, d.chain, header, state); err {
	case nil:
		return nil
	default:
		return consensus.ErrWhenSigningHeader
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
	parent := d.chain.GetBlock(parentHeader.Hash(), parentHeader.Number.Uint64())

	num := parentHeader.Number
	impeachHeader := &types.Header{
		ParentHash: parentHeader.Hash(),
		Number:     num.Add(num, common.Big1),
		GasLimit:   parent.GasLimit(),
		Extra:      make([]byte, extraVanity),
		Time:       new(big.Int).Add(parent.Time(), big.NewInt(int64(d.ImpeachTimeout())+int64(d.config.Period))),
		Coinbase:   common.Address{},
		Nonce:      types.BlockNonce{},
		Difficulty: DporDifficulty,
		MixHash:    common.Hash{},
		StateRoot:  parentHeader.StateRoot,
	}

	impeach := types.NewBlock(impeachHeader, []*types.Transaction{}, []*types.Receipt{})

	return impeach, nil
}

// EcrecoverSigs recovers signer address and corresponding signature, it ignores empty signature and return empty
// addresses if one of the sigs are illegal
func (d *Dpor) EcrecoverSigs(header *types.Header, state consensus.State) ([]common.Address, []types.DporSignature, error) {
	var hashBytes []byte

	sigs := header.Dpor.Sigs
	addrs := make([]common.Address, 0, len(sigs))
	validSigs := make([]types.DporSignature, 0, len(sigs))
	for _, sig := range sigs {
		if !sig.IsEmpty() {
			if state == consensus.Preprepared {
				hashBytes = d.dh.sigHash(header, []byte{'P'}).Bytes()
			} else {
				hashBytes = d.dh.sigHash(header, []byte{}).Bytes()
			}
			proposerPubKey, err := crypto.Ecrecover(hashBytes, sig[:])
			if err != nil {
				return []common.Address{}, []types.DporSignature{}, err
			}

			addr := common.Address{}
			copy(addr[:], crypto.Keccak256(proposerPubKey[1:])[12:])
			addrs = append(addrs, addr)
			validSigs = append(validSigs, sig)
		}
	}
	return addrs, validSigs, nil
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
