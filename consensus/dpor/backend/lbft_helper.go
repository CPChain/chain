package backend

import (
	"sync"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
	lru "github.com/hashicorp/golang-lru"
)

type BlockOrHeader struct {
	block  *types.Block
	header *types.Header
}

func newBOHFromHeader(header *types.Header) *BlockOrHeader {
	return &BlockOrHeader{
		header: header,
	}
}

func newBOHFromBlock(block *types.Block) *BlockOrHeader {
	return &BlockOrHeader{
		block: block,
	}
}

func (bh *BlockOrHeader) IsBlock() bool {
	return bh != nil && bh.block != nil
}

func (bh *BlockOrHeader) IsHeader() bool {
	return bh != nil && bh.header != nil
}

func (bh *BlockOrHeader) Number() uint64 {
	if bh.IsBlock() {
		return bh.block.NumberU64()
	} else if bh.IsHeader() {
		return bh.header.Number.Uint64()
	}
	return uint64(0)
}

func (bh *BlockOrHeader) Hash() common.Hash {
	if bh.IsBlock() {
		return bh.block.Hash()
	} else if bh.IsHeader() {
		return bh.header.Hash()
	}
	return common.Hash{}
}

type signaturesOfBlock struct {
	signatures map[common.Address]types.DporSignature
	lock       sync.RWMutex
}

func newSignaturesOfBlock() *signaturesOfBlock {
	return &signaturesOfBlock{
		signatures: make(map[common.Address]types.DporSignature),
	}
}

func (sb *signaturesOfBlock) setSignature(signer common.Address, signature types.DporSignature) {
	sb.lock.Lock()
	defer sb.lock.Unlock()

	sb.signatures[signer] = signature
}

func (sb *signaturesOfBlock) getSignature(signer common.Address) (types.DporSignature, bool) {
	sb.lock.RLock()
	defer sb.lock.RUnlock()

	signature, ok := sb.signatures[signer]
	return signature, ok
}

func (sb *signaturesOfBlock) count() int {
	sb.lock.RLock()
	defer sb.lock.RUnlock()

	for signer := range sb.signatures {
		log.Debug("", "signer", signer.Hex())
	}

	return len(sb.signatures)
}

type signaturesForBlockCaches struct {
	db                  database.Database
	signaturesForBlocks *lru.ARCCache
	lock                sync.RWMutex
}

func newSignaturesForBlockCaches(db database.Database) *signaturesForBlockCaches {
	sigCaches, _ := lru.NewARC(100)
	return &signaturesForBlockCaches{
		db:                  db,
		signaturesForBlocks: sigCaches,
	}
}

// getSignaturesCountOf returns the number of signatures for given block identifier
func (sc *signaturesForBlockCaches) getSignaturesCountOf(bi blockIdentifier) int {
	sc.lock.RLock()
	defer sc.lock.RUnlock()

	sigs, ok := sc.signaturesForBlocks.Get(bi)
	if sigs != nil && ok {

		log.Debug("counting signatures of block", "number", bi.number, "hash", bi.hash.Hex())

		return sigs.(*signaturesOfBlock).count()
	}

	signatures := newSignaturesOfBlock()
	bytes, err := sc.db.Get(bi.hash.Bytes())
	if err == nil {
		err = rlp.DecodeBytes(bytes, &signatures)
		if err != nil {
			log.Debug("err when decoding signatures from byte retrieved from db", "err", err, "number", bi.number, "hash", bi.hash.Hex())
		}
		return signatures.count()
	}

	return 0
}

// addSignatureFor adds a signature to signature caches
func (sc *signaturesForBlockCaches) addSignatureFor(bi blockIdentifier, signer common.Address, signature types.DporSignature) {
	sc.lock.Lock()
	defer sc.lock.Unlock()

	signatures := newSignaturesOfBlock()
	sigs, ok := sc.signaturesForBlocks.Get(bi)
	if sigs != nil && ok {
		signatures = sigs.(*signaturesOfBlock)
	}

	signatures.setSignature(signer, signature)
	sc.signaturesForBlocks.Add(bi, signatures)

	bytes, err := rlp.EncodeToBytes(signatures)
	if err != nil {
		log.Warn("err when encoding signatures to bytes", "err", err, "number", bi.number, "hash", bi.hash.Hex())
		return
	}

	err = sc.db.Put(bi.hash.Bytes(), bytes)
	if err != nil {
		log.Warn("err when saving signatures to db", "err", err, "number", bi.number, "hash", bi.hash.Hex())
	}

	log.Warn("saved signatures to db", "number", bi.number, "hash", bi.hash.Hex())
}

func (sc *signaturesForBlockCaches) getSignatureFor(bi blockIdentifier, signer common.Address) (types.DporSignature, bool) {
	sc.lock.RLock()
	defer sc.lock.RUnlock()

	sigs, ok := sc.signaturesForBlocks.Get(bi)
	if sigs != nil && ok {
		return sigs.(*signaturesOfBlock).getSignature(signer)
	}
	return types.DporSignature{}, false
}

func (sc *signaturesForBlockCaches) cacheSignaturesFromHeader(signers []common.Address, signatures []types.DporSignature, validators []common.Address, header *types.Header) error {
	bi := blockIdentifier{
		hash:   header.Hash(),
		number: header.Number.Uint64(),
	}

	for i, s := range signers {
		isV := false
		for _, v := range validators {
			if s == v {
				isV = true
			}
		}
		if isV {
			sc.addSignatureFor(bi, s, signatures[i])
		}
	}

	return nil
}

func (sc *signaturesForBlockCaches) writeSignaturesToHeader(validators []common.Address, header *types.Header) error {
	bi := blockIdentifier{
		hash:   header.Hash(),
		number: header.Number.Uint64(),
	}

	for i, v := range validators {
		if signature, ok := sc.getSignatureFor(bi, v); ok {
			header.Dpor.Sigs[i] = signature
		}
	}

	return nil
}
