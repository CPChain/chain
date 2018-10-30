package ethapi

import (
	"fmt"

	"bitbucket.org/cpchain/chain/api/v1/common"

	"bitbucket.org/cpchain/chain/api/v1/txpool"

	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"google.golang.org/grpc"

	"bitbucket.org/cpchain/chain/types"
	"github.com/golang/protobuf/ptypes/empty"
	"golang.org/x/net/context"
)

// TransactionPoolReader offers and API for the transaction pool. It only operates on data that is non confidential.
type TransactionPoolReader struct {
	b Backend
}

// NewTransactionPoolReader creates a new tx pool service that gives information about the transaction pool.
func NewTransactionPoolReader(b Backend) *TransactionPoolReader {
	return &TransactionPoolReader{b}
}

// IsPublic if public default
func (t *TransactionPoolReader) IsPublic() bool {
	return true
}

// Namespace namespace
func (t *TransactionPoolReader) Namespace() string {
	return "txpool"
}

// RegisterServer register api to grpc
func (t *TransactionPoolReader) RegisterServer(s *grpc.Server) {
	txpool.RegisterTransactionPoolReaderServer(s, t)
}

// RegisterGateway register api to restfull json
func (t *TransactionPoolReader) RegisterGateway(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	txpool.RegisterTransactionPoolReaderHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// Content returns the transactions contained within the transaction pool.
func (s *TransactionPoolReader) Content(ctx context.Context, in *empty.Empty) (*txpool.TxPool, error) {
	// var content txpool.TxPool
	content := &txpool.TxPool{
		PendingTxPool: &txpool.AccountNonceTxPool{
			AccountNonceTxPool: make(map[string]*txpool.NonceTx),
		},
		QueuedTxPool: &txpool.AccountNonceTxPool{
			AccountNonceTxPool: make(map[string]*txpool.NonceTx),
		},
	}
	pending, queue := s.b.TxPoolContent()

	// Flatten the pending transactions
	for account, txs := range pending {
		dump := &txpool.NonceTx{NonceTx: make(map[string]*common.RpcTransaction)}
		for _, tx := range txs {
			dump.NonceTx[fmt.Sprintf("%d", tx.Nonce())] = newGRPCPendingTransaction(tx)
		}
		content.PendingTxPool.AccountNonceTxPool[account.Hex()] = dump
	}
	// Flatten the queued transactions
	for account, txs := range queue {
		dump := &txpool.NonceTx{NonceTx: make(map[string]*common.RpcTransaction)}
		for _, tx := range txs {
			dump.NonceTx[fmt.Sprintf("%d", tx.Nonce())] = newGRPCPendingTransaction(tx)
		}
		content.QueuedTxPool.AccountNonceTxPool[account.Hex()] = dump
	}
	return content, nil
}

// Status returns the number of pending and queued transaction in the pool.
func (s *TransactionPoolReader) Status(ctx context.Context, in *empty.Empty) (*txpool.StatusInfo, error) {
	var out txpool.StatusInfo
	out.Status = make(map[string]uint64)

	pending, queue := s.b.Stats()
	out.Status["pending"] = uint64(pending)
	out.Status["queued"] = uint64(queue)

	return &out, nil
}

// inspect retrieves the content of the transaction pool and flattens it into an
// easily inspectable list.
func (s *TransactionPoolReader) Inspect(ctx context.Context, in *empty.Empty) (*txpool.TxStringPool, error) {
	content := &txpool.TxStringPool{
		PendingTxStringPool: &txpool.AccountNonceTxStringPool{
			AccountNonceTxStringPool: make(map[string]*txpool.NonceTxString),
		},
		QueuedTxStringPool: &txpool.AccountNonceTxStringPool{
			AccountNonceTxStringPool: make(map[string]*txpool.NonceTxString),
		},
	}
	pending, queue := s.b.TxPoolContent()

	// Define a formatter to flatten a transaction into a string
	var format = func(tx *types.Transaction) string {
		if to := tx.To(); to != nil {
			return fmt.Sprintf("%s: %v wei + %v gas × %v wei", tx.To().Hex(), tx.Value(), tx.Gas(), tx.GasPrice())
		}
		return fmt.Sprintf("contract creation: %v wei + %v gas × %v wei", tx.Value(), tx.Gas(), tx.GasPrice())
	}
	// Flatten the pending transactions
	for account, txs := range pending {
		dump := &txpool.NonceTxString{TxString: make(map[string]string)}
		for _, tx := range txs {
			dump.TxString[fmt.Sprintf("%d", tx.Nonce())] = format(tx)
		}
		content.PendingTxStringPool.AccountNonceTxStringPool[account.Hex()] = dump
	}
	// Flatten the queued transactions
	for account, txs := range queue {
		dump := &txpool.NonceTxString{TxString: make(map[string]string)}
		for _, tx := range txs {
			dump.TxString[fmt.Sprintf("%d", tx.Nonce())] = format(tx)
		}
		content.PendingTxStringPool.AccountNonceTxStringPool[account.Hex()] = dump
	}
	return content, nil
}
