package ethapi

import (
	"context"

	"bitbucket.org/cpchain/chain/api/protos/v1"
	"bitbucket.org/cpchain/chain/core/rawdb"
	"bitbucket.org/cpchain/chain/rpc"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/golang/protobuf/ptypes/empty"
)

// ChainReaderApiImpl provides an API to access the Ethereum blockchain.
// It offers only methods that operate on public data that is freely available to anyone.
type ChainReaderApiImpl struct {
	b Backend
}

// NewChainReaderImpl creates a new Ethereum blockchain API.
func NewChainReaderImpl(b Backend) *ChainReaderApiImpl {
	return &ChainReaderApiImpl{b}
}

// GetBlockCount returns the block number of the chain head.
func (c *ChainReaderApiImpl) GetBlockCount(ctx context.Context, req *empty.Empty) (*protos.BlockNumber, error) {
	header, _ := c.b.HeaderByNumber(context.Background(), rpc.LatestBlockNumber) // latest header should always be available
	return &protos.BlockNumber{BlockNumber: header.Number.Uint64()}, nil
}

func (c *ChainReaderApiImpl) IsPublic() bool {
	return true
}

func (c *ChainReaderApiImpl) Namespace() string {
	return "eth"
}

// GetBalance returns the amount of wei for the given address in the state of the
// given block number. The rpc.LatestBlockNumber and rpc.PendingBlockNumber meta
// block numbers are also allowed.
func (s *ChainReaderApiImpl) GetBalance(ctx context.Context, req *protos.ChainReaderRequest) (*protos.Balance, error) {
	state, _, err := s.b.StateAndHeaderByNumber(ctx, rpc.BlockNumber(req.BlockNumber), req.IsFull)
	if state == nil || err != nil {
		return nil, err
	}
	balance := (*hexutil.Big)(state.GetBalance(common.HexToAddress(req.Address)))
	return &protos.Balance{Balance: balance.String()}, state.Error()
}

// newGRPCTransaction returns a transaction that will serialize to the RPC
// representation, with the given location metadata set (if available).
func newGRPCTransaction(tx *types.Transaction, blockHash common.Hash, blockNumber uint64, index uint64) *protos.Transaction {
	var signer types.Signer = types.FrontierSigner{}
	if tx.Protected() {
		signer = types.NewPrivTxSupportEIP155Signer(tx.ChainId())
	}
	from, _ := types.Sender(signer, tx)
	v, r, s := tx.RawSignatureValues()

	result := &protos.Transaction{
		From:     from.String(),
		Gas:      tx.Gas(),
		GasPrice: tx.GasPrice().Uint64(),
		Hash:     tx.Hash().String(),
		Input:    tx.Data(),
		Nonce:    tx.Nonce(),
		To:       tx.To().String(),
		Value:    tx.Value().String(),
		V:        v.String(),
		R:        r.String(),
		S:        s.String(),
	}
	if blockHash != (common.Hash{}) {
		result.BlockHash = blockHash.String()
		result.BlockNumber = blockNumber
		result.TransactionIndex = index
	}
	return result
}

// newRPCPendingTransaction returns a pending transaction that will serialize to the RPC representation
func newGRPCPendingTransaction(tx *types.Transaction) *protos.Transaction {
	return newGRPCTransaction(tx, common.Hash{}, 0, 0)
}

// newGRPCTransactionFromBlockIndex returns a transaction that will serialize to the RPC representation.
func newGRPCTransactionFromBlockIndex(b *types.Block, index uint64) *protos.Transaction {
	txs := b.Transactions()
	if index >= uint64(len(txs)) {
		return nil
	}
	return newGRPCTransaction(txs[index], b.Hash(), b.NumberU64(), index)
}

// newGRPCTransactionFromBlockHash returns a transaction that will serialize to the RPC representation.
func newGRPCTransactionFromBlockHash(b *types.Block, hash common.Hash) *protos.Transaction {
	for idx, tx := range b.Transactions() {
		if tx.Hash() == hash {
			return newGRPCTransactionFromBlockIndex(b, uint64(idx))
		}
	}
	return nil
}

// GRPCMarshalBlock converts the given block to the RPC output which depends on fullTx. If inclTx is true transactions are
// returned. When fullTx is true the returned block contains full transaction details, otherwise it will only contain
// transaction hashes.
func GRPCMarshalBlock(b *types.Block, inclTx bool, fullTx bool) (*protos.Block, error) {
	head := b.Header() // copies the header once
	block := &protos.Block{
		Number:           head.Number.Uint64(),
		Hash:             b.Hash().String(),
		ParentHash:       head.ParentHash.String(),
		Nonce:            head.Nonce.Uint64(),
		MixHash:          head.MixHash.String(),
		LogsBloom:        head.LogsBloom.Bytes(),
		StateRoot:        head.StateRoot.String(),
		Miner:            head.Coinbase.String(),
		Difficulty:       head.Difficulty.Uint64(),
		ExtraData:        head.Extra,
		Size:             uint64(head.Size()),
		GasLimit:         head.GasLimit,
		GasUsed:          head.GasUsed,
		Timestamp:        head.Time.String(),
		TransactionsRoot: head.TxsRoot.String(),
		ReceiptsRoot:     head.ReceiptsRoot.String(),
	}

	if inclTx {
		formatTx := func(tx *types.Transaction) (*protos.Transaction, error) {
			return &protos.Transaction{TxHash: tx.Hash().String()}, nil
		}
		if fullTx {
			formatTx = func(tx *types.Transaction) (*protos.Transaction, error) {
				return newGRPCTransactionFromBlockHash(b, tx.Hash()), nil
			}
		}
		txs := b.Transactions()
		block.Transactions = make([]*protos.Transaction, len(txs))
		var err error
		for i, tx := range txs {
			if block.Transactions[i], err = formatTx(tx); err != nil {
				return nil, err
			}
		}
	}

	return block, nil
}

// rpcOutputBlock uses the generalized output filler, then adds the total difficulty field, which requires
// a `PublicBlockchainAPI`.
func (s *ChainReaderApiImpl) grpcOutputBlock(b *types.Block, inclTx bool, fullTx bool) (*protos.Block, error) {
	block, err := GRPCMarshalBlock(b, inclTx, fullTx)
	if err != nil {
		return nil, err
	}
	return block, err
}

// GetBlockByNumber returns the requested block. When blockNr is -1 the chain head is returned. When fullTx is true all
// transactions in the block are returned in full detail, otherwise only the transaction hash is returned.
func (s *ChainReaderApiImpl) GetBlockByNumber(ctx context.Context, req *protos.ChainReaderRequest) (*protos.Block, error) {
	block, err := s.b.BlockByNumber(ctx, rpc.BlockNumber(req.BlockNumber))
	if block != nil {
		response, err := s.grpcOutputBlock(block, true, req.IsFull)
		if err == nil && rpc.BlockNumber(req.BlockNumber) == rpc.PendingBlockNumber {
			// Pending blocks need to nil out a few fields
			response.Hash = ""
			response.Nonce = 0
			response.Miner = ""
		}
		return response, err
	}
	return &protos.Block{}, err
}

// GetBlockByHash returns the requested block. When fullTx is true all transactions in the block are returned in full
// detail, otherwise only the transaction hash is returned.
func (s *ChainReaderApiImpl) GetBlockByHash(ctx context.Context, req *protos.ChainReaderRequest) (*protos.Block, error) {
	block, err := s.b.GetBlock(ctx, common.HexToHash(req.BlockHash))
	if block != nil {
		return s.grpcOutputBlock(block, true, req.IsFull)
	}
	return &protos.Block{}, err
}

// TransactionReader exposes methods for the RPC interface
type TransactionReader struct {
	b         Backend
	nonceLock *AddrLocker
}

// NewTransactionReader a new RPC service with methods specific for the transaction pool.
func NewTransactionReader(b Backend, nonceLock *AddrLocker) *TransactionReader {
	return &TransactionReader{b, nonceLock}
}

// GetBlockTransactionCountByNumber returns the number of transactions in the block with the given block number.
func (s *TransactionReader) GetTransactionCountByBlockNumber(ctx context.Context, blockNr rpc.BlockNumber) (*protos.TransactionCount, error) {
	if block, _ := s.b.BlockByNumber(ctx, blockNr); block != nil {
		return &protos.TransactionCount{TransactionCount: uint64(len(block.Transactions()))}, nil
	}
	return &protos.TransactionCount{}, nil
}

// GetBlockTransactionCountByHash returns the number of transactions in the block with the given hash.
func (s *TransactionReader) GetTransactionCountByBlockHash(ctx context.Context, blockHash common.Hash) (*protos.TransactionCount, error) {
	if block, _ := s.b.GetBlock(ctx, blockHash); block != nil {
		return &protos.TransactionCount{TransactionCount: uint64(len(block.Transactions()))}, nil
	}
	return &protos.TransactionCount{}, nil
}

// GetTransactionByBlockNumberAndIndex returns the transaction for the given block number and index.
func (s *TransactionReader) GetTransactionByBlockNumberAndIndex(ctx context.Context, req *protos.TransactionPoolReaderRequest) (*protos.Transaction, error) {
	if block, _ := s.b.BlockByNumber(ctx, rpc.BlockNumber(req.BlockNumber)); block != nil {
		return newGRPCTransactionFromBlockIndex(block, req.Index), nil
	}
	return &protos.Transaction{}, nil
}

// GetTransactionByBlockHashAndIndex returns the transaction for the given block hash and index.
func (s *TransactionReader) GetTransactionByBlockHashAndIndex(ctx context.Context, req *protos.TransactionPoolReaderRequest) (*protos.Transaction, error) {
	if block, _ := s.b.GetBlock(ctx, common.HexToHash(req.BlockHash)); block != nil {
		return newGRPCTransactionFromBlockIndex(block, req.Index), nil
	}
	return &protos.Transaction{}, nil
}

// GetRawTransactionByBlockNumberAndIndex returns the bytes of the transaction for the given block number and index.
func (s *TransactionReader) GetRawTransactionByBlockNumberAndIndex(ctx context.Context, req *protos.TransactionPoolReaderRequest) (*protos.RawTransaction, error) {
	if block, _ := s.b.BlockByNumber(ctx, rpc.BlockNumber(req.BlockNumber)); block != nil {
		return &protos.RawTransaction{RawTransaction: newRPCRawTransactionFromBlockIndex(block, req.Index)}, nil
	}
	return &protos.RawTransaction{}, nil
}

// GetRawTransactionByBlockHashAndIndex returns the bytes of the transaction for the given block hash and index.
func (s *TransactionReader) GetRawTransactionByBlockHashAndIndex(ctx context.Context, req *protos.TransactionPoolReaderRequest) (*protos.RawTransaction, error) {
	if block, _ := s.b.GetBlock(ctx, common.HexToHash(req.BlockHash)); block != nil {
		return &protos.RawTransaction{RawTransaction: newRPCRawTransactionFromBlockIndex(block, req.Index)}, nil
	}
	return &protos.RawTransaction{}, nil
}

// GetTransactionCount returns the number of transactions the given address has sent for the given block number
func (s *TransactionReader) GetTransactionCount(ctx context.Context, req *protos.TransactionPoolReaderRequest) (*protos.TransactionCount, error) {
	state, _, err := s.b.StateAndHeaderByNumber(ctx, rpc.BlockNumber(req.BlockNumber), false)
	if state == nil || err != nil {
		return nil, err
	}
	nonce := state.GetNonce(common.HexToAddress(req.Address))
	return &protos.TransactionCount{TransactionCount: nonce}, nil
}

// GetTransactionByHash returns the transaction for the given hash
func (s *TransactionReader) GetTransactionByHash(ctx context.Context, txHash *protos.TransactionHash) (*protos.Transaction, error) {
	// Try to return an already finalized transaction
	if tx, blockHash, blockNumber, index := rawdb.ReadTransaction(s.b.ChainDb(), common.HexToHash(txHash.TransactionHash)); tx != nil {
		return newGRPCTransaction(tx, blockHash, blockNumber, index), nil
	}
	// No finalized transaction, try to retrieve it from the pool
	if tx := s.b.GetPoolTransaction(common.HexToHash(txHash.TransactionHash)); tx != nil {
		return newGRPCPendingTransaction(tx), nil
	}
	// Transaction unknown, return as such
	return &protos.Transaction{}, nil
}

// GetRawTransactionByHash returns the bytes of the transaction for the given hash.
func (s *TransactionReader) GetRawTransactionByHash(ctx context.Context, hash common.Hash) (hexutil.Bytes, error) {
	var tx *types.Transaction

	// Retrieve a finalized transaction, or a pooled otherwise
	if tx, _, _, _ = rawdb.ReadTransaction(s.b.ChainDb(), hash); tx == nil {
		if tx = s.b.GetPoolTransaction(hash); tx == nil {
			// Transaction not found anywhere, abort
			return nil, nil
		}
	}
	// Serialize to RLP and return
	return rlp.EncodeToBytes(tx)
}

// GetTransactionReceipt returns the transaction receipt for the given transaction hash.
func (s *TransactionReader) GetTransactionReceipt(ctx context.Context, txHash *protos.TransactionHash) (*protos.Receipt, error) {
	tx, blockHash, blockNumber, index := rawdb.ReadTransaction(s.b.ChainDb(), common.HexToHash(txHash.TransactionHash))
	if tx == nil {
		return &protos.Receipt{}, nil
	}

	var receipt *types.Receipt
	if tx.IsPrivate() {
		receipt, _ = s.b.GetPrivateReceipt(ctx, tx.Hash())
		if receipt == nil {
			return nil, nil
		}
	} else {
		receipts, err := s.b.GetReceipts(ctx, blockHash)
		if err != nil {
			return nil, err
		}
		if len(receipts) <= int(index) {
			return nil, nil
		}
		receipt = receipts[index]
	}

	var signer types.Signer = types.FrontierSigner{}
	if tx.Protected() {
		signer = types.NewPrivTxSupportEIP155Signer(tx.ChainId())
	}
	from, _ := types.Sender(signer, tx)

	result := &protos.Receipt{
		BlockHash:        blockHash.String(),
		BlockNumber:      blockNumber,
		TransactionHash:  txHash.TransactionHash,
		TransactionIndex: index,
		From:             from.String(),
		To:               tx.To().String(),
		GasUsed:          receipt.GasUsed,
		Logs:             make([]*protos.Log, len(receipt.Logs)),
		LogsBloom:        receipt.Bloom.Bytes(),
	}

	for _, log := range receipt.Logs {
		l := &protos.Log{
			Removed:     log.Removed,
			BlockNumber: log.BlockNumber,
			TxIndex:     uint64(log.TxIndex),
			BlockHash:   log.BlockHash.String(),
			Index:       uint32(log.Index),
			Address:     log.Address.String(),
			TxHash:      log.TxHash.String(),
			Data:        log.Data,
			Topics:      make([]string, len(log.Topics)),
		}
		for _, t := range log.Topics {
			l.Topics = append(l.Topics, t.String())
		}
		result.Logs = append(result.Logs, l)
	}

	// Assign receipt status or post state.
	if len(receipt.PostState) > 0 {
		result.Root = receipt.PostState
	} else {
		result.Status = receipt.Status
	}
	if receipt.Logs == nil {
		result.Logs = []*protos.Log{}
	}
	// If the ContractAddress is 20 0x0 bytes, assume it is not a contract creation
	if receipt.ContractAddress != (common.Address{}) {
		result.ContractAddress = receipt.ContractAddress.String()
	}
	return result, nil
}
