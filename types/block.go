// Copyright 2014 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

// Package types contains data types related to Ethereum consensus.
package types

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"math/big"
	"sort"
	"sync/atomic"
	"time"
	"unsafe"

	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/rlp"
)

const (
	DporSigLength = 65
)

var (
	EmptyRootHash = DeriveSha(Transactions{})
)

// A BlockNonce is a 64-bit hash which proves (combined with the
// mix-hash) that a sufficient amount of computation has been carried
// out on a block.
type BlockNonce [8]byte

// EncodeNonce converts the given integer to a block nonce.
func EncodeNonce(i uint64) BlockNonce {
	var n BlockNonce
	binary.BigEndian.PutUint64(n[:], i)
	return n
}

// Uint64 returns the integer value of a block nonce.
func (n BlockNonce) Uint64() uint64 {
	return binary.BigEndian.Uint64(n[:])
}

// MarshalText encodes n as a hex string with 0x prefix.
func (n BlockNonce) MarshalText() ([]byte, error) {
	return hexutil.Bytes(n[:]).MarshalText()
}

// UnmarshalText implements encoding.TextUnmarshaler.
func (n *BlockNonce) UnmarshalText(input []byte) error {
	return hexutil.UnmarshalFixedText("BlockNonce", input, n[:])
}

//go:generate gencodec -type Header -field-override headerMarshaling -out gen_header_json.go

const (
	extraVanity = 32 // Fixed number of extra-data prefix bytes reserved for signer vanity
	extraSeal   = 65 // Fixed number of extra-data suffix bytes reserved for signer seal
)

// Header represents a block header in the Ethereum blockchain.
type Header struct {
	ParentHash   common.Hash    `json:"parentHash"       gencodec:"required"`
	Coinbase     common.Address `json:"miner"            gencodec:"required"`
	StateRoot    common.Hash    `json:"stateRoot"        gencodec:"required"`
	TxsRoot      common.Hash    `json:"transactionsRoot" gencodec:"required"`
	ReceiptsRoot common.Hash    `json:"receiptsRoot"     gencodec:"required"`
	LogsBloom    Bloom          `json:"logsBloom"        gencodec:"required"`
	Difficulty   *big.Int       `json:"difficulty"       gencodec:"required"`
	Number       *big.Int       `json:"number"           gencodec:"required"`
	GasLimit     uint64         `json:"gasLimit"         gencodec:"required"`
	GasUsed      uint64         `json:"gasUsed"          gencodec:"required"`
	Time         *big.Int       `json:"timestamp"        gencodec:"required"`
	Extra        []byte         `json:"extraData"        gencodec:"required"`
	MixHash      common.Hash    `json:"mixHash"          gencodec:"required"`
	Nonce        BlockNonce     `json:"nonce"            gencodec:"required"`
	Dpor         DporSnap       `json:"dpor"             gencodec:"required"`
}

type DporSignature [DporSigLength]byte

func HexToDporSig(s string) DporSignature {
	var a DporSignature
	copy(a[:], common.FromHex(s))
	return a
}

func (d *DporSignature) IsEmpty() bool {
	return bytes.Equal(d[:], bytes.Repeat([]byte{0x00}, DporSigLength))
}

func (m *DporSignature) UnmarshalText(text []byte) error {
	text = bytes.TrimPrefix(text, []byte("0x"))
	if _, err := hex.Decode(m[:], text); err != nil {
		fmt.Println(err)
		return fmt.Errorf("invalid hex storage key/value %q", text)
	}
	return nil
}

func (m *DporSignature) MarshalText() ([]byte, error) {
	return hexutil.Bytes(m[:]).MarshalText()
}

type DporSnap struct {
	Seal       DporSignature    // the signature of the block's producer
	Sigs       []DporSignature  // the signatures of validators to endorse the block
	Proposers  []common.Address // current proposers committee
	Validators []common.Address // updated validator committee in next epoch if it is not nil. Keep the same to current if it is nil.
}

// field type overrides for gencodec
type headerMarshaling struct {
	Difficulty *hexutil.Big
	Number     *hexutil.Big
	GasLimit   hexutil.Uint64
	GasUsed    hexutil.Uint64
	Time       *hexutil.Big
	Extra      hexutil.Bytes
	Hash       common.Hash `json:"hash"` // adds call to Hash() in MarshalJSON
	Dpor       *DporSnap
}

// Hash returns the block hash of the header, which is simply the keccak256 hash of its
// RLP encoding.
func (h *Header) Hash() common.Hash {
	return sigHash(h)
}

// sigHash returns hash of header
func sigHash(header *Header) (hash common.Hash) {
	hasher := sha3.NewKeccak256()
	err := rlp.Encode(hasher, []interface{}{
		header.ParentHash,
		header.Coinbase,
		header.StateRoot,
		header.TxsRoot,
		header.ReceiptsRoot,
		header.LogsBloom,
		header.Difficulty,
		header.Number,
		header.GasLimit,
		header.GasUsed,
		header.Time,
		header.Dpor.Proposers,
		header.Dpor.Validators,
		header.Extra,
		header.MixHash,
		header.Nonce,
	})
	if err != nil {
		log.Error("invalid hash encoding", "error", err)
		return common.Hash{}
	}
	hasher.Sum(hash[:0])
	return hash
}

// HashNoNonce returns the hash which is used as input for the proof-of-work search.
func (h *Header) HashNoNonce() common.Hash {
	return rlpHash([]interface{}{
		h.ParentHash,
		h.Coinbase,
		h.StateRoot,
		h.TxsRoot,
		h.ReceiptsRoot,
		h.LogsBloom,
		h.Difficulty,
		h.Number,
		h.GasLimit,
		h.GasUsed,
		h.Time,
		h.Dpor.Proposers,
		h.Dpor.Validators,
		h.Extra,
	})
}

// Size returns the approximate memory used by all internal contents. It is used
// to approximate and limit the memory consumption of various caches.
func (h *Header) Size() common.StorageSize {
	dporSize := common.StorageSize(len(h.Dpor.Proposers))*common.StorageSize(unsafe.Sizeof(common.Address{})) +
		common.StorageSize(len(h.Dpor.Sigs))*common.StorageSize(unsafe.Sizeof(DporSignature{})) +
		common.StorageSize(len(h.Dpor.Validators))*common.StorageSize(unsafe.Sizeof(common.Address{})) +
		common.StorageSize(unsafe.Sizeof(h.Dpor.Seal))

	return common.StorageSize(unsafe.Sizeof(*h)) + common.StorageSize(len(h.Extra)+(h.Difficulty.BitLen()+
		h.Number.BitLen()+h.Time.BitLen())/8) + dporSize
}

func rlpHash(x interface{}) (h common.Hash) {
	hw := sha3.NewKeccak256()
	rlp.Encode(hw, x)
	hw.Sum(h[:0])
	return h
}

// Body is a simple (mutable, non-safe) data container for storing and moving
// a block's data contents (transactions and uncles) together.
type Body struct {
	Transactions []*Transaction
}

// Block represents an entire block in the Ethereum blockchain.
type Block struct {
	header       *Header
	transactions Transactions

	// caches
	hash atomic.Value
	size atomic.Value

	// Td is used by package core to store the total difficulty
	// of the chain up to and including the block.
	td *big.Int

	// These fields are used to track inter-peer block relay.
	ReceivedAt   time.Time
	ReceivedFrom interface{}
}

// DeprecatedTd is an old relic for extracting the TD of a block. It is in the
// code solely to facilitate upgrading the database from the old format to the
// new, after which it should be deleted. Do not use!
func (b *Block) DeprecatedTd() *big.Int {
	return b.td
}

// [deprecated by eth/63]
// StorageBlock defines the RLP encoding of a Block stored in the
// state database. The StorageBlock encoding contains fields that
// would otherwise need to be recomputed.
type StorageBlock Block

// "external" block encoding. used for eth protocol, etc.
type extblock struct {
	Header *Header
	Txs    []*Transaction
}

// [deprecated by eth/63]
// "storage" block encoding. used for database.
type storageblock struct {
	Header *Header
	Txs    []*Transaction
	TD     *big.Int
}

// NewBlock creates a new block. The input data is copied,
// changes to header and to the field values will not affect the
// block.
//
// The values of TxsRoot, UncleHash, ReceiptsRoot and LogsBloom in header
// are ignored and set to values derived from the given txs, uncles
// and receipts.
func NewBlock(header *Header, txs []*Transaction, receipts []*Receipt) *Block {
	b := &Block{header: CopyHeader(header), td: new(big.Int)}

	// TODO: panic if len(txs) != len(receipts)
	if len(txs) == 0 {
		b.header.TxsRoot = EmptyRootHash
	} else {
		b.header.TxsRoot = DeriveSha(Transactions(txs))
		b.transactions = make(Transactions, len(txs))
		copy(b.transactions, txs)
	}

	if len(receipts) == 0 {
		b.header.ReceiptsRoot = EmptyRootHash
	} else {
		b.header.ReceiptsRoot = DeriveSha(Receipts(receipts))
		b.header.LogsBloom = CreateBloom(receipts)
	}

	return b
}

// NewBlockWithHeader creates a block with the given header data. The
// header data is copied, changes to header and to the field values
// will not affect the block.
func NewBlockWithHeader(header *Header) *Block {
	return &Block{header: CopyHeader(header)}
}

// CopyHeader creates a deep copy of a block header to prevent side effects from
// modifying a header variable.
func CopyHeader(h *Header) *Header {
	cpy := *h
	if cpy.Time = new(big.Int); h.Time != nil {
		cpy.Time.Set(h.Time)
	}
	if cpy.Difficulty = new(big.Int); h.Difficulty != nil {
		cpy.Difficulty.Set(h.Difficulty)
	}
	if cpy.Number = new(big.Int); h.Number != nil {
		cpy.Number.Set(h.Number)
	}
	if len(h.Extra) > 0 {
		cpy.Extra = make([]byte, len(h.Extra))
		copy(cpy.Extra, h.Extra)
	}
	cpy.Dpor = *CopyDporSnap(&h.Dpor)
	return &cpy
}

func CopyDporSnap(d *DporSnap) *DporSnap {
	// copy DporSnap
	cpy := new(DporSnap)
	// copy DporSnap.Proposers
	cpy.Proposers = make([]common.Address, len(d.Proposers))
	for i := 0; i < len(d.Proposers); i++ {
		copy(cpy.Proposers[i][:], d.Proposers[i][:])
	}
	// copy DporSnap.Sigs
	cpy.Sigs = make([]DporSignature, len(d.Sigs))
	for i := 0; i < len(d.Sigs); i++ {
		copy(cpy.Sigs[i][:], d.Sigs[i][:])
	}
	// copy DporSnap.Seal
	copy(cpy.Seal[:], d.Seal[:])
	// copy DporSnap.Validators
	cpy.Validators = make([]common.Address, len(d.Validators))
	for i := 0; i < len(d.Validators); i++ {
		copy(cpy.Validators[i][:], d.Validators[i][:])
	}
	return cpy
}

// DecodeRLP decodes the Ethereum
func (b *Block) DecodeRLP(s *rlp.Stream) error {
	var eb extblock
	_, size, _ := s.Kind()
	if err := s.Decode(&eb); err != nil {
		return err
	}
	b.header, b.transactions = eb.Header, eb.Txs
	b.size.Store(common.StorageSize(rlp.ListSize(size)))
	return nil
}

// EncodeRLP serializes b into the Ethereum RLP block format.
func (b *Block) EncodeRLP(w io.Writer) error {
	return rlp.Encode(w, extblock{
		Header: b.header,
		Txs:    b.transactions,
	})
}

// [deprecated by eth/63]
func (b *StorageBlock) DecodeRLP(s *rlp.Stream) error {
	var sb storageblock
	if err := s.Decode(&sb); err != nil {
		return err
	}
	b.header, b.transactions, b.td = sb.Header, sb.Txs, sb.TD
	return nil
}

// TODO: copies

func (b *Block) Transactions() Transactions { return b.transactions }

func (b *Block) Transaction(hash common.Hash) *Transaction {
	for _, transaction := range b.transactions {
		if transaction.Hash() == hash {
			return transaction
		}
	}
	return nil
}

func (b *Block) Number() *big.Int     { return new(big.Int).Set(b.header.Number) }
func (b *Block) GasLimit() uint64     { return b.header.GasLimit }
func (b *Block) GasUsed() uint64      { return b.header.GasUsed }
func (b *Block) Difficulty() *big.Int { return new(big.Int).Set(b.header.Difficulty) }
func (b *Block) Time() *big.Int       { return new(big.Int).Set(b.header.Time) }

func (b *Block) NumberU64() uint64         { return b.header.Number.Uint64() }
func (b *Block) MixHash() common.Hash      { return b.header.MixHash }
func (b *Block) Nonce() uint64             { return binary.BigEndian.Uint64(b.header.Nonce[:]) }
func (b *Block) LogsBloom() Bloom          { return b.header.LogsBloom }
func (b *Block) Coinbase() common.Address  { return b.header.Coinbase }
func (b *Block) StateRoot() common.Hash    { return b.header.StateRoot }
func (b *Block) ParentHash() common.Hash   { return b.header.ParentHash }
func (b *Block) TxsRoot() common.Hash      { return b.header.TxsRoot }
func (b *Block) ReceiptsRoot() common.Hash { return b.header.ReceiptsRoot }
func (b *Block) Extra() []byte             { return common.CopyBytes(b.header.Extra) }
func (b *Block) Dpor() DporSnap            { return b.header.Dpor }

func (b *Block) RefHeader() *Header { return b.header } // TODO: fix it.
func (b *Block) Header() *Header    { return CopyHeader(b.header) }

// Body returns the non-header content of the block.
func (b *Block) Body() *Body { return &Body{b.transactions} }

func (b *Block) HashNoNonce() common.Hash {
	return b.header.HashNoNonce()
}

// Size returns the true RLP encoded storage size of the block, either by encoding
// and returning it, or returning a previsouly cached value.
func (b *Block) Size() common.StorageSize {
	if size := b.size.Load(); size != nil {
		return size.(common.StorageSize)
	}
	c := writeCounter(0)
	rlp.Encode(&c, b)
	b.size.Store(common.StorageSize(c))
	return common.StorageSize(c)
}

type writeCounter common.StorageSize

func (c *writeCounter) Write(b []byte) (int, error) {
	*c += writeCounter(len(b))
	return len(b), nil
}

// WithSeal returns a new block with the data from b but the header replaced with
// the sealed one.
func (b *Block) WithSeal(header *Header) *Block {
	cpy := *header

	return &Block{
		header:       &cpy,
		transactions: b.transactions,
	}
}

// WithBody returns a new block with the given transaction and uncle contents.
func (b *Block) WithBody(transactions []*Transaction) *Block {
	block := &Block{
		header:       CopyHeader(b.header),
		transactions: make([]*Transaction, len(transactions)),
	}
	copy(block.transactions, transactions)
	return block
}

// Hash returns the keccak256 hash of b's header.
// The hash is computed on the first call and cached thereafter.
func (b *Block) Hash() common.Hash {
	if hash := b.hash.Load(); hash != nil {
		return hash.(common.Hash)
	}
	v := b.header.Hash()
	b.hash.Store(v)
	return v
}

type Blocks []*Block

type BlockBy func(b1, b2 *Block) bool

func (self BlockBy) Sort(blocks Blocks) {
	bs := blockSorter{
		blocks: blocks,
		by:     self,
	}
	sort.Sort(bs)
}

type blockSorter struct {
	blocks Blocks
	by     func(b1, b2 *Block) bool
}

func (self blockSorter) Len() int { return len(self.blocks) }
func (self blockSorter) Swap(i, j int) {
	self.blocks[i], self.blocks[j] = self.blocks[j], self.blocks[i]
}
func (self blockSorter) Less(i, j int) bool { return self.by(self.blocks[i], self.blocks[j]) }

func Number(b1, b2 *Block) bool { return b1.header.Number.Cmp(b2.header.Number) < 0 }
