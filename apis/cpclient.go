package gapis

import (
	"bytes"
	"context"
	"crypto/tls"
	"crypto/x509"
	"encoding/gob"
	"encoding/json"
	"errors"
	"fmt"
	"io/ioutil"
	"math/big"
	"path/filepath"

	"github.com/golang/protobuf/ptypes/any"

	pb "bitbucket.org/cpchain/chain/proto/chain_reader"

	"bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/golang/protobuf/ptypes/empty"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials"
)

var (
	cliCrt = "client.crt"
	cliKey = "client.key"
	ca     = "ca.crt"
)

type Client struct {
	certificate tls.Certificate
	certPool    *x509.CertPool
	c           *grpc.ClientConn
}

func NewClient(endpoint, datadir string, useTls bool) (*Client, error) {
	var err error
	opts := []grpc.DialOption{
		grpc.WithInsecure(),
	}
	c := &Client{}

	if useTls {
		c.certPool, err = createCertPool()
		if err != nil {
			return nil, err
		}

		// Load the certificates from disk
		c.certificate, err = tls.LoadX509KeyPair(crt, key)
		if err != nil {
			return nil, fmt.Errorf("could not load server key pair: %s", err.Error())
		}

		ca, err := ioutil.ReadFile(filepath.Join(datadir, ca))
		if err != nil {
			return nil, fmt.Errorf("could not read ca certificate: %s", err)
		}

		if ok := c.certPool.AppendCertsFromPEM(ca); !ok {
			return nil, errors.New("failed to append ca certs")
		}

		// Create the TLS credentials
		creds := credentials.NewTLS(&tls.Config{
			ServerName:   endpoint,
			Certificates: []tls.Certificate{c.certificate},
			RootCAs:      c.certPool,
		})
		opts = append(opts, grpc.WithTransportCredentials(creds))
	}

	c.c, err = grpc.Dial(endpoint, opts...)
	if err != nil {
		return nil, err
	}
	return c, nil
}

func New(c *grpc.ClientConn) *Client {
	return &Client{c: c}
}

func (c *Client) Close() {
	c.c.Close()
}

// Blockchain Access

// BlockByHash returns the given full block.
//
// Note that loading full blocks requires two requests. Use HeaderByHash
// if you don't need all transactions or uncle headers.
func (c *Client) BlockByHash(ctx context.Context, hash common.Hash) (*types.Block, error) {
	args := &pb.PublicBlockChainAPIRequest{
		FullTx:    true,
		BlockHash: hash.Bytes(),
	}
	return c.getBlock(ctx, "/protos_chain.PublicBlockChainAPI/GetBlockByHash", args)
}

// BlockByNumber returns a block from the current canonical chain. If number is nil, the
// latest known block is returned.
//
// Note that loading full blocks requires two requests. Use HeaderByNumber
// if you don't need all transactions or uncle headers.
func (c *Client) BlockByNumber(ctx context.Context, number *big.Int) (*types.Block, error) {
	args := &pb.PublicBlockChainAPIRequest{
		FullTx:      true,
		BlockNumber: number.Uint64(),
	}
	return c.getBlock(ctx, "/protos_chain.PublicBlockChainAPI/GetBlockByNumber", args)
}

type rpcBlock struct {
	Hash         common.Hash      `json:"hash"`
	Transactions []rpcTransaction `json:"transactions"`
}

// TODO: @sangh new instance
func (c *Client) getBlock(ctx context.Context, method string, args *pb.PublicBlockChainAPIRequest) (*types.Block, error) {
	var reply pb.PublicBlockChainAPIReply
	err := c.c.Invoke(ctx, method, args, reply)
	raw := json.RawMessage(reply.BlockInfo.GetValue())
	if err != nil {
		return nil, err
	} else if len(raw) == 0 {
		return nil, ethereum.NotFound
	}
	// Decode header and transactions.
	var head *types.Header
	var body rpcBlock
	if err := json.Unmarshal(raw, &head); err != nil {
		return nil, err
	}
	if err := json.Unmarshal(raw, &body); err != nil {
		return nil, err
	}
	// Quick-verify transaction and uncle lists. This mostly helps with debugging the server.
	if head.TxsRoot == types.EmptyRootHash && len(body.Transactions) > 0 {
		return nil, fmt.Errorf("server returned non-empty transaction list but block header indicates no transactions")
	}
	if head.TxsRoot != types.EmptyRootHash && len(body.Transactions) == 0 {
		return nil, fmt.Errorf("server returned empty transaction list but block header indicates transactions")
	}

	// Fill the sender cache of transactions in the block.
	txs := make([]*types.Transaction, len(body.Transactions))
	for i, tx := range body.Transactions {
		if tx.From != nil {
			setSenderFromServer(tx.tx, *tx.From, body.Hash)
		}
		txs[i] = tx.tx
	}
	return types.NewBlockWithHeader(head).WithBody(txs), nil
}

// HeaderByHash returns the block header with the given hash.
func (c *Client) HeaderByHash(ctx context.Context, hash common.Hash) (*types.Header, error) {
	args := &pb.PublicBlockChainAPIRequest{
		FullTx:    false,
		BlockHash: hash.Bytes(),
	}
	var reply pb.PublicBlockChainAPIReply
	err := c.c.Invoke(ctx, "/protos_chain.PublicBlockChainAPI/GetBlockByHash", args, reply)
	var head *types.Header
	if err != nil {
		return nil, err
	}
	raw := (json.RawMessage)(reply.BlockInfo.GetValue())
	if err := json.Unmarshal(raw, head); err != nil {
		return nil, err
	}
	if err == nil && head == nil {
		err = ethereum.NotFound
	}
	return head, err
}

// HeaderByNumber returns a block header from the current canonical chain. If number is
// nil, the latest known header is returned.
func (c *Client) HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error) {
	args := &pb.PublicBlockChainAPIRequest{
		BlockNumber: number.Uint64(),
		FullTx:      false,
	}
	var reply pb.PublicBlockChainAPIReply
	err := c.c.Invoke(ctx, "/protos_chain.PublicBlockChainAPI/GetBlockByNumber", args, reply)
	if err != nil {
		return nil, err
	}

	raw := (json.RawMessage)(reply.BlockInfo.GetValue())
	var head *types.Header
	if err := json.Unmarshal(raw, head); err != nil {
		return nil, err
	}
	if err == nil && head == nil {
		err = ethereum.NotFound
	}
	return head, err
}

type rpcTransaction struct {
	tx *types.Transaction
	txExtraInfo
}

type txExtraInfo struct {
	BlockNumber *string         `json:"blockNumber,omitempty"`
	BlockHash   *common.Hash    `json:"blockHash,omitempty"`
	From        *common.Address `json:"from,omitempty"`
}

func (tx *rpcTransaction) UnmarshalJSON(msg []byte) error {
	if err := json.Unmarshal(msg, &tx.tx); err != nil {
		return err
	}
	return json.Unmarshal(msg, &tx.txExtraInfo)
}

// TransactionByHash returns the transaction with the given hash.
func (c *Client) TransactionByHash(ctx context.Context, hash common.Hash) (tx *types.Transaction, isPending bool, err error) {
	args := pb.PublicTransactionPoolAPIRequest{
		BlockHash: hash.Bytes(),
	}
	var reply pb.PublicTransactionPoolAPIReply
	err = c.c.Invoke(ctx, "/protos_chain.PublicTransactionPoolAPI/GetTransactionByHash(ctx)", args, reply)
	if err != nil {
		return nil, false, err
	}
	var json *rpcTransaction
	err = json.UnmarshalJSON(reply.RpcTransaction.GetValue())
	if err != nil {
		return nil, false, err
	}
	if err != nil {
		return nil, false, err
	} else if json == nil {
		return nil, false, ethereum.NotFound
	} else if _, r, _ := json.tx.RawSignatureValues(); r == nil {
		return nil, false, fmt.Errorf("server returned transaction without signature")
	}
	if json.From != nil && json.BlockHash != nil {
		setSenderFromServer(json.tx, *json.From, *json.BlockHash)
	}
	return json.tx, json.BlockNumber == nil, nil
}

// TransactionSender returns the sender address of the given transaction. The transaction
// must be known to the remote node and included in the blockchain at the given block and
// index. The sender is the one derived by the protocol at the time of inclusion.
//
// There is a fast-path for transactions retrieved by TransactionByHash and
// TransactionInBlock. Getting their sender address can be done without an RPC interaction.
func (c *Client) TransactionSender(ctx context.Context, tx *types.Transaction, block common.Hash, index uint) (common.Address, error) {
	// Try to load the address from the cache.
	sender, err := types.Sender(&senderFromServer{blockhash: block}, tx)
	if err == nil {
		return sender, nil
	}
	var meta struct {
		Hash common.Hash
		From common.Address
	}
	args := pb.PublicTransactionPoolAPIRequest{
		BlockHash: block.Bytes(),
		Index:     uint64(index),
	}
	var reply pb.PublicTransactionPoolAPIReply
	if err = c.c.Invoke(ctx, "/protos_chain.PublicTransactionPoolAPI/GetTransactionByBlockHashAndIndex", args, reply); err != nil {
		return common.Address{}, err
	}

	var json *rpcTransaction
	if err := json.UnmarshalJSON(reply.RpcTransaction.GetValue()); err != nil {
		return common.Address{}, err
	}
	if meta.Hash == (common.Hash{}) || meta.Hash != tx.Hash() {
		return common.Address{}, errors.New("wrong inclusion block/index")
	}
	return meta.From, nil
}

// TransactionCount returns the total number of transactions in the given block.
func (c *Client) TransactionCount(ctx context.Context, blockHash common.Hash) (uint, error) {
	args := pb.PublicTransactionPoolAPIRequest{
		BlockHash: blockHash.Bytes(),
	}
	var reply pb.PublicTransactionPoolAPIReply
	err := c.c.Invoke(ctx, "/protos_chain.PublicTransactionPoolAPI/GetBlockTransactionCountByHash", args, reply)
	return uint(reply.Count), err
}

// TransactionInBlock returns a single transaction at index in the given block.
func (c *Client) TransactionInBlock(ctx context.Context, blockHash common.Hash, index uint) (*types.Transaction, error) {
	args := pb.PublicTransactionPoolAPIRequest{
		BlockHash: blockHash.Bytes(),
		Index:     uint64(index),
	}
	var reply pb.PublicTransactionPoolAPIReply
	err := c.c.Invoke(ctx, "/protos_chain.PublicTransactionPoolAPI/GetTransactionByBlockHashAndIndex", args, reply)
	if err != nil {
		return nil, err
	}
	var json *rpcTransaction
	if err := json.UnmarshalJSON(reply.RpcTransaction.GetValue()); err != nil {
		return nil, err
	}
	if json == nil {
		return nil, ethereum.NotFound
	} else if _, r, _ := json.tx.RawSignatureValues(); r == nil {
		return nil, fmt.Errorf("server returned transaction without signature")
	}
	if json.From != nil && json.BlockHash != nil {
		setSenderFromServer(json.tx, *json.From, *json.BlockHash)
	}
	return json.tx, err
}

// TransactionReceipt returns the receipt of a transaction by transaction hash.
// Note that the receipt is not available for pending transactions.
func (c *Client) TransactionReceipt(ctx context.Context, txHash common.Hash) (*types.Receipt, error) {
	var r *types.Receipt
	args := pb.PublicTransactionPoolAPIRequest{
		TxHash: txHash.Bytes(),
	}
	var reply *pb.PublicTransactionPoolAPIReply
	err := c.c.Invoke(ctx, "/protos_chain.PublicTransactionPoolAPI/GetTransactionReceipt", args, reply)
	if err != nil {
		return nil, err
	}

	if err := r.UnmarshalJSON(reply.Fields.GetValue()); err != nil {
		return nil, err
	}

	if r == nil {
		return nil, ethereum.NotFound
	}
	return r, err
}

func toBlockNumArg(number *big.Int) string {
	if number == nil {
		return "latest"
	}
	return hexutil.EncodeBig(number)
}

type rpcProgress struct {
	StartingBlock hexutil.Uint64
	CurrentBlock  hexutil.Uint64
	HighestBlock  hexutil.Uint64
	PulledStates  hexutil.Uint64
	KnownStates   hexutil.Uint64
}

// SyncProgress retrieves the current progress of the sync algorithm. If there's
// no sync currently running, it returns nil.
func (c *Client) SyncProgress(ctx context.Context) (*ethereum.SyncProgress, error) {
	var reply *pb.PublicEthereumAPIReply
	if err := c.c.Invoke(ctx, "/protos_chain.PublicEthereumAPI/Syncing", &empty.Empty{}, reply); err != nil {
		return nil, err
	}
	if reply.IsOk != nil {
		return nil, nil
	}

	raw := json.RawMessage(reply.SyncInfo.GetValue())
	// Handle the possible response types
	var syncing bool
	if err := json.Unmarshal(raw, &syncing); err == nil {
		return nil, nil // Not syncing (always false)
	}
	var progress *rpcProgress
	if err := json.Unmarshal(raw, &progress); err != nil {
		return nil, err
	}
	return &ethereum.SyncProgress{
		StartingBlock: uint64(progress.StartingBlock),
		CurrentBlock:  uint64(progress.CurrentBlock),
		HighestBlock:  uint64(progress.HighestBlock),
		PulledStates:  uint64(progress.PulledStates),
		KnownStates:   uint64(progress.KnownStates),
	}, nil
}

// SubscribeNewHead subscribes to notifications about the current blockchain head
// on the given channel.
// TODO: @sangh
// func (c *Client) SubscribeNewHead(ctx context.Context, ch chan<- *types.Header) (ethereum.Subscription, error) {
// 	return c.c.EthSubscribe(ctx, ch, "newHeads")
// }

// State Access

// NetworkID returns the network ID (also known as the chain ID) for this chain.
func (c *Client) NetworkID(ctx context.Context) (*big.Int, error) {
	return nil, nil
	// version := new(big.Int)
	// var ver string
	// if err := c.c.Invoke(ctx, &ver, "net_version"); err != nil {
	// 	return nil, err
	// }
	// if _, ok := version.SetString(ver, 10); !ok {
	// 	return nil, fmt.Errorf("invalid net_version result %q", ver)
	// }
	// return version, nil
}

// BalanceAt returns the wei balance of the given account.
// The block number can be nil, in which case the balance is taken from the latest known block.
func (c *Client) BalanceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (*big.Int, error) {
	args := pb.PublicBlockChainAPIRequest{
		Address:     account.Bytes(),
		BlockNumber: blockNumber.Uint64(),
	}
	var reply pb.PublicBlockChainAPIReply
	err := c.c.Invoke(ctx, "/protos_chain.PublicBlockChainAPIServer/GetBalance", args, reply)
	if err != nil {
		return nil, err
	}

	buf := bytes.NewBuffer(reply.Balance)
	dec := gob.NewDecoder(buf)
	var result hexutil.Big
	if err := dec.Decode(&result); err != nil {
		return nil, err
	}
	return (*big.Int)(&result), err
}

// StorageAt returns the value of key in the contract storage of the given account.
// The block number can be nil, in which case the value is taken from the latest known block.
func (c *Client) StorageAt(ctx context.Context, account common.Address, key common.Hash, blockNumber *big.Int) ([]byte, error) {
	args := &pb.PublicBlockChainAPIRequest{
		Address:     account.Bytes(),
		Key:         key.String(),
		BlockNumber: blockNumber.Uint64(),
	}
	var reply pb.PublicBlockChainAPIReply
	err := c.c.Invoke(ctx, "/protos_chain.PublicBlockChainAPI/GetStorageAt", args, reply)
	if err != nil {
		return nil, err
	}
	return reply.Storage, nil
}

// CodeAt returns the contract code of the given account.
// The block number can be nil, in which case the code is taken from the latest known block.
func (c *Client) CodeAt(ctx context.Context, account common.Address, blockNumber *big.Int) ([]byte, error) {
	args := pb.PublicBlockChainAPIRequest{
		Address:     account.Bytes(),
		BlockNumber: blockNumber.Uint64(),
	}
	var reply pb.PublicBlockChainAPIReply
	err := c.c.Invoke(ctx, "/protos_chain.PublicBlockChainAPI/GetCode", args, reply)
	if err != nil {
		return nil, err
	}
	return reply.Code, err
}

// NonceAt returns the account nonce of the given account.
// The block number can be nil, in which case the nonce is taken from the latest known block.
func (c *Client) NonceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (uint64, error) {
	args := pb.PublicTransactionPoolAPIRequest{
		Address:     account.Bytes(),
		BlockNumber: blockNumber.Uint64(),
	}
	var reply pb.PublicTransactionPoolAPIReply
	err := c.c.Invoke(ctx, "/protos_chain.PublicTransactionPoolAPI/GetTransactionCount", args, reply)
	return reply.Count, err
}

// Filters

// FilterLogs executes a filter query.
func (c *Client) FilterLogs(ctx context.Context, q ethereum.FilterQuery) ([]types.Log, error) {
	// var result []types.Log
	// err := c.c.Invoke(ctx, &result, "eth_getLogs", toFilterArg(q))
	// return result, err
	return nil, nil
}

// SubscribeFilterLogs subscribes to the results of a streaming filter query.
// func (c *Client) SubscribeFilterLogs(ctx context.Context, q ethereum.FilterQuery, ch chan<- types.Log) (ethereum.Subscription, error) {
// return c.c.EthSubscribe(ctx, ch, "logs", toFilterArg(q))
// }

func toFilterArg(q ethereum.FilterQuery) interface{} {
	arg := map[string]interface{}{
		"fromBlock": toBlockNumArg(q.FromBlock),
		"toBlock":   toBlockNumArg(q.ToBlock),
		"address":   q.Addresses,
		"topics":    q.Topics,
	}
	if q.FromBlock == nil {
		arg["fromBlock"] = "0x0"
	}
	return arg
}

// Pending State

// PendingBalanceAt returns the wei balance of the given account in the pending state.
func (c *Client) PendingBalanceAt(ctx context.Context, account common.Address) (*big.Int, error) {
	// var result hexutil.Big
	// args := pb.PublicBlockChainAPIRequest{
	// 	Address:account.Bytes(),
	// }
	// err := c.c.Invoke(ctx, "/protos_chain.PublicBlockChainAPI/GetBalance", account, "pending")
	// return (*big.Int)(&result), err
	return nil, nil
}

// PendingStorageAt returns the value of key in the contract storage of the given account in the pending state.
func (c *Client) PendingStorageAt(ctx context.Context, account common.Address, key common.Hash) ([]byte, error) {
	// var result hexutil.Bytes
	// err := c.c.CallContext(ctx, "eth_getStorageAt", account, key, "pending")
	// return result, err
	return nil, nil
}

// PendingCodeAt returns the contract code of the given account in the pending state.
func (c *Client) PendingCodeAt(ctx context.Context, account common.Address) ([]byte, error) {
	// var result hexutil.Bytes
	// err := ec.c.CallContext(ctx, "eth_getCode", account, "pending")
	// return result, err
	return nil, nil
}

// PendingNonceAt returns the account nonce of the given account in the pending state.
// This is the nonce that should be used for the next transaction.
func (c *Client) PendingNonceAt(ctx context.Context, account common.Address) (uint64, error) {
	// var result hexutil.Uint64
	// err := c.c.Invoke(ctx, "eth_getTransactionCount", account, "pending")
	// return uint64(result), err
	return 0, nil
}

// PendingTransactionCount returns the total number of transactions in the pending state.
func (c *Client) PendingTransactionCount(ctx context.Context) (uint, error) {
	// var num hexutil.Uint
	// err := ec.c.CallContext(ctx, &num, "eth_getBlockTransactionCountByNumber", "pending")
	// return uint(num), err
	return 0, nil
}

// TODO: SubscribePendingTransactions (needs server side)

// Contract Calling

// CallContract executes a message call transaction, which is directly executed in the VM
// of the node, but never mined into the blockchain.
//
// blockNumber selects the block height at which the call runs. It can be nil, in which
// case the code is taken from the latest known block. Note that state from very old
// blocks might not be available.
func (c *Client) CallContract(ctx context.Context, msg ethereum.CallMsg, blockNumber *big.Int) ([]byte, error) {
	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(&msg); err != nil {
		return nil, nil
	}
	args := pb.PublicBlockChainAPIRequest{
		Args: &any.Any{
			Value: buf.Bytes(),
		},
		BlockNumber: blockNumber.Uint64(),
	}
	var reply pb.PublicBlockChainAPIReply
	err := c.c.Invoke(ctx, "/protos_chain.PublicBlockChainAPI/Call", args, reply)
	if err != nil {
		return nil, err
	}
	return reply.Result, nil
}

// PendingCallContract executes a message call transaction using the EVM.
// The state seen by the contract call is the pending state.
func (c *Client) PendingCallContract(ctx context.Context, msg ethereum.CallMsg) ([]byte, error) {
	// var hex hexutil.Bytes
	// err := ec.c.CallContext(ctx, &hex, "eth_call", toCallArg(msg), "pending")
	// if err != nil {
	// 	return nil, err
	// }
	// return hex, nil
	return nil, nil
}

// SuggestGasPrice retrieves the currently suggested gas price to allow a timely
// execution of a transaction.
func (c *Client) SuggestGasPrice(ctx context.Context) (*big.Int, error) {
	var reply pb.PublicEthereumAPIReply
	if err := c.c.Invoke(ctx, "/protos_chain.PublicEthereumAPI/GasPrice", &empty.Empty{}, reply); err != nil {
		return nil, err
	}

	var gasprice big.Int
	buf := bytes.NewBuffer(reply.GasPrice)
	dec := gob.NewDecoder(buf)
	if err := dec.Decode(&gasprice); err != nil {
		return nil, err
	}
	return &gasprice, nil
}

// EstimateGas tries to estimate the gas needed to execute a specific transaction based on
// the current pending state of the backend blockchain. There is no guarantee that this is
// the true gas limit requirement as other transactions may be added or removed by miners,
// but it should provide a basis for setting a reasonable default.
func (c *Client) EstimateGas(ctx context.Context, msg ethereum.CallMsg) (uint64, error) {
	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(&msg); err != nil {
		return 0, err
	}

	args := &pb.PublicBlockChainAPIRequest{
		Args: &any.Any{
			Value: buf.Bytes(),
		},
	}
	var reply pb.PublicBlockChainAPIReply
	err := c.c.Invoke(ctx, "/protos_chain.PublicBlockChainAPI/EstimateGas", args, reply)
	if err != nil {
		return 0, err
	}
	return reply.EstimateGas, nil
}

// SendTransaction injects a signed transaction into the pending pool for execution.
//
// If the transaction was a contract creation use the TransactionReceipt method to get the
// contract address after the transaction has been mined.
func (c *Client) SendTransaction(ctx context.Context, tx *types.Transaction) error {
	data, err := rlp.EncodeToBytes(tx)
	if err != nil {
		return err
	}
	args := &pb.PublicTransactionPoolAPIRequest{
		EncodedTx: data,
	}
	var reply pb.PublicTransactionPoolAPIReply
	return c.c.Invoke(ctx, "/protos_chain.PublicTransactionPoolAPI/SendRawTransaction", args, reply)
}

func toCallArg(msg ethereum.CallMsg) interface{} {
	arg := map[string]interface{}{
		"from": msg.From,
		"to":   msg.To,
	}
	if len(msg.Data) > 0 {
		arg["data"] = hexutil.Bytes(msg.Data)
	}
	if msg.Value != nil {
		arg["value"] = (*hexutil.Big)(msg.Value)
	}
	if msg.Gas != 0 {
		arg["gas"] = hexutil.Uint64(msg.Gas)
	}
	if msg.GasPrice != nil {
		arg["gasPrice"] = (*hexutil.Big)(msg.GasPrice)
	}
	return arg
}
