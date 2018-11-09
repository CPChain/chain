package ethapi

import (
	"fmt"

	"bitbucket.org/cpchain/chain/api/grpc/v1/common"
	"bitbucket.org/cpchain/chain/api/grpc/v1/txpool"
	"bitbucket.org/cpchain/chain/types"
	"github.com/golang/protobuf/ptypes/empty"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

// TxPoolReader offers and API for the transaction pool. It only operates on data that is non confidential.
type TxPoolReader struct {
	b Backend
}

// NewTxPoolReader creates a new tx pool service that gives information about the transaction pool.
func NewTxPoolReader(b Backend) *TxPoolReader {
	return &TxPoolReader{b}
}

// IsPublic if public default
func (t *TxPoolReader) IsPublic() bool {
	return true
}

// Namespace namespace
func (t *TxPoolReader) Namespace() string {
	return "txpool"
}

// RegisterServer register api to grpc
func (t *TxPoolReader) RegisterServer(s *grpc.Server) {
	txpool.RegisterTxPoolReaderServer(s, t)
}

// RegisterJsonRpc register api to restfull json
func (t *TxPoolReader) RegisterJsonRpc(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	txpool.RegisterTxPoolReaderHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// Content returns the transactions contained within the transaction pool.
func (s *TxPoolReader) Content(ctx context.Context, in *empty.Empty) (*txpool.TxPool, error) {
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
func (s *TxPoolReader) Status(ctx context.Context, in *empty.Empty) (*txpool.StatusInfo, error) {
	var out txpool.StatusInfo
	out.Status = make(map[string]uint64)

	pending, queue := s.b.Stats()
	out.Status["pending"] = uint64(pending)
	out.Status["queued"] = uint64(queue)

	return &out, nil
}

// inspect retrieves the content of the transaction pool and flattens it into an
// easily inspectable list.
func (s *TxPoolReader) Inspect(ctx context.Context, in *empty.Empty) (*txpool.TxStringPool, error) {
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
