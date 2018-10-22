// Copyright 2015 The go-ethereum Authors
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

package ethapi

import (
	"bytes"
	"encoding/gob"
	"errors"
	"fmt"
	"math/big"
	"strings"
	"time"

	"github.com/golang/protobuf/ptypes/any"
	"github.com/golang/protobuf/ptypes/wrappers"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/ethash"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/rawdb"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/crypto"
	"bitbucket.org/cpchain/chain/private"
	pb "bitbucket.org/cpchain/chain/proto/chain_reader"
	"bitbucket.org/cpchain/chain/rpc"
	"bitbucket.org/cpchain/chain/types"
	"github.com/davecgh/go-spew/spew"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/common/math"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/golang/protobuf/ptypes/empty"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"github.com/syndtr/goleveldb/leveldb"
	"github.com/syndtr/goleveldb/leveldb/util"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
)

// const (
// 	defaultGasPrice = 50 * configs.Shannon
// )

// var (
// 	InvalidPrivateTxErr = errors.New("Private transaction should have participants defined and payload data.")
// )

// PublicEthereumAPIServer provides an APIServer to access Ethereum related information.
// It offers only methods that operate on public data that is freely available to anyone.
type PublicEthereumAPIServer struct {
	b Backend
}

// NewPublicEthereumAPIServer creates a new Ethereum protocol APIServer.
func NewPublicEthereumAPIServer(b Backend) *PublicEthereumAPIServer {
	return &PublicEthereumAPIServer{b}
}

func (api *PublicEthereumAPIServer) RegisterServer(s *grpc.Server) {
	pb.RegisterPublicEthereumAPIServer(s, api)
}

func (api *PublicEthereumAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	pb.RegisterPublicEthereumAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// GasPrice returns a suggestion for a gas price.
func (s *PublicEthereumAPIServer) GasPrice(ctx context.Context, in *empty.Empty) (*pb.PublicEthereumAPIReply, error) {
	price, err := s.b.SuggestPrice(ctx)
	if err != nil {
		return nil, err
	}
	return &pb.PublicEthereumAPIReply{GasPrice: price.Bytes()}, nil
}

// ProtocolVersion returns the current Ethereum protocol version this node supports
func (s *PublicEthereumAPIServer) ProtocolVersion(ctx context.Context, in *empty.Empty) (*pb.PublicEthereumAPIReply, error) {
	return &pb.PublicEthereumAPIReply{Version: uint32(s.b.ProtocolVersion())}, nil
}

// Syncing returns false in case the node is currently not syncing with the network. It can be up to date or has not
// yet received the latest block headers from its pears. In case it is synchronizing:
// - startingBlock: block number this node started to synchronise from
// - currentBlock:  block number this node is currently importing
// - highestBlock:  block number of the highest block header this node has received from peers
// - pulledStates:  number of state entries processed until now
// - knownStates:   number of known state entries that still need to be pulled
func (s *PublicEthereumAPIServer) Syncing(ctx context.Context, in *empty.Empty) (*pb.PublicEthereumAPIReply, error) {
	progress := s.b.Downloader().Progress()

	// Return not syncing if the synchronisation already completed
	if progress.CurrentBlock >= progress.HighestBlock {
		return &pb.PublicEthereumAPIReply{
			IsOk: false,
		}, nil
	}

	// Otherwise gather the block sync stats
	syncInfo := map[string]interface{}{
		"startingBlock": hexutil.Uint64(progress.StartingBlock),
		"currentBlock":  hexutil.Uint64(progress.CurrentBlock),
		"highestBlock":  hexutil.Uint64(progress.HighestBlock),
		"pulledStates":  hexutil.Uint64(progress.PulledStates),
		"knownStates":   hexutil.Uint64(progress.KnownStates),
	}

	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(syncInfo); err != nil {
		return nil, err
	}

	return &pb.PublicEthereumAPIReply{
		SyncInfo: &any.Any{Value: buf.Bytes()},
	}, nil
}

// PublicTxPoolAPIServer offers and APIServer for the transaction pool. It only operates on data that is non confidential.
type PublicTxPoolAPIServer struct {
	b Backend
}

// NewPublicTxPoolAPIServer creates a new tx pool service that gives information about the transaction pool.
func NewPublicTxPoolAPIServer(b Backend) *PublicTxPoolAPIServer {
	return &PublicTxPoolAPIServer{b}
}

func (api *PublicTxPoolAPIServer) RegisterServer(s *grpc.Server) {
	pb.RegisterPublicTxPoolAPIServer(s, api)
}

func (api *PublicTxPoolAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	pb.RegisterPublicTxPoolAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// Content returns the transactions contained within the transaction pool.
func (s *PublicTxPoolAPIServer) Content(ctx context.Context, in *empty.Empty) (*pb.PublicTxPoolAPIReply, error) {
	content := map[string]map[string]map[string]*RPCTransaction{
		"pending": make(map[string]map[string]*RPCTransaction),
		"queued":  make(map[string]map[string]*RPCTransaction),
	}
	pending, queue := s.b.TxPoolContent()

	// Flatten the pending transactions
	for account, txs := range pending {
		dump := make(map[string]*RPCTransaction)
		for _, tx := range txs {
			dump[fmt.Sprintf("%d", tx.Nonce())] = newRPCPendingTransaction(tx)
		}
		content["pending"][account.Hex()] = dump
	}
	// Flatten the queued transactions
	for account, txs := range queue {
		dump := make(map[string]*RPCTransaction)
		for _, tx := range txs {
			dump[fmt.Sprintf("%d", tx.Nonce())] = newRPCPendingTransaction(tx)
		}
		content["queued"][account.Hex()] = dump
	}

	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(content); err != nil {
		return nil, err
	}
	return &pb.PublicTxPoolAPIReply{
		Content: &any.Any{
			Value: buf.Bytes(),
		},
	}, nil
}

// Status returns the number of pending and queued transaction in the pool.
func (s *PublicTxPoolAPIServer) Status(ctx context.Context, in *empty.Empty) (*pb.PublicTxPoolAPIReply, error) {
	pending, queue := s.b.Stats()
	status := map[string]uint64{
		"pending": uint64(pending),
		"queued":  uint64(queue),
	}
	return &pb.PublicTxPoolAPIReply{
		Status: status,
	}, nil
}

// Inspect retrieves the content of the transaction pool and flattens it into an
// easily inspectable list.
func (s *PublicTxPoolAPIServer) Inspect(ctx context.Context, in *empty.Empty) (*pb.PublicTxPoolAPIReply, error) {
	content := map[string]map[string]map[string]string{
		"pending": make(map[string]map[string]string),
		"queued":  make(map[string]map[string]string),
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
		dump := make(map[string]string)
		for _, tx := range txs {
			dump[fmt.Sprintf("%d", tx.Nonce())] = format(tx)
		}
		content["pending"][account.Hex()] = dump
	}
	// Flatten the queued transactions
	for account, txs := range queue {
		dump := make(map[string]string)
		for _, tx := range txs {
			dump[fmt.Sprintf("%d", tx.Nonce())] = format(tx)
		}
		content["queued"][account.Hex()] = dump
	}

	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(content); err != nil {
		return nil, err
	}
	return &pb.PublicTxPoolAPIReply{
		Inspect: &any.Any{
			Value: buf.Bytes(),
		},
	}, nil
}

// PublicAccountAPIServer provides an APIServer to access accounts managed by this node.
// It offers only methods that can retrieve accounts.
type PublicAccountAPIServer struct {
	am *accounts.Manager
}

// NewPublicAccountAPIServer creates a new PublicAccountAPIServer.
func NewPublicAccountAPIServer(am *accounts.Manager) *PublicAccountAPIServer {
	return &PublicAccountAPIServer{am: am}
}
func (api *PublicAccountAPIServer) RegisterServer(s *grpc.Server) {
	pb.RegisterPublicAccountAPIServer(s, api)
}

func (api *PublicAccountAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	pb.RegisterPublicAccountAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// Accounts returns the collection of accounts this node manages
func (s *PublicAccountAPIServer) Accounts(ctx context.Context, in *empty.Empty) (*pb.PublicAccountAPIReply, error) {
	addresses := make([]common.Address, 0) // return [] instead of nil if empty
	for _, wallet := range s.am.Wallets() {
		for _, account := range wallet.Accounts() {
			addresses = append(addresses, account.Address)
		}
	}

	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(addresses); err != nil {
		return nil, err
	}

	return &pb.PublicAccountAPIReply{
		Accounts: &any.Any{
			Value: buf.Bytes(),
		},
	}, nil
}

// PrivateAccountAPIServer provides an APIServer to access accounts managed by this node.
// It offers methods to create, (un)lock en list accounts. Some methods accept
// passwords and are therefore considered private by default.
type PrivateAccountAPIServer struct {
	am        *accounts.Manager
	nonceLock *AddrLocker
	b         Backend
}

// NewPrivateAccountAPIServer create a new PrivateAccountAPIServer.
func NewPrivateAccountAPIServer(b Backend, nonceLock *AddrLocker) *PrivateAccountAPIServer {
	return &PrivateAccountAPIServer{
		am:        b.AccountManager(),
		nonceLock: nonceLock,
		b:         b,
	}
}

func (api *PrivateAccountAPIServer) RegisterServer(s *grpc.Server) {
	pb.RegisterPrivateAccountAPIServer(s, api)
}

func (api *PrivateAccountAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	pb.RegisterPublicEthereumAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// ListAccounts will return a list of addresses for accounts this node manages.
func (s *PrivateAccountAPIServer) ListAccounts(ctx context.Context, in *empty.Empty) (*pb.PrivateAccountAPIReply, error) {
	addresses := make([]common.Address, 0) // return [] instead of nil if empty
	for _, wallet := range s.am.Wallets() {
		for _, account := range wallet.Accounts() {
			addresses = append(addresses, account.Address)
		}
	}
	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(addresses); err != nil {
		return nil, err
	}

	return &pb.PrivateAccountAPIReply{
		AccountAddresses: &any.Any{
			Value: buf.Bytes(),
		},
	}, nil
}

// ListWallets will return a list of wallets this node manages.
func (s *PrivateAccountAPIServer) ListWallets(ctx context.Context, in *empty.Empty) (reply *pb.PrivateAccountAPIReply, err error) {
	wallets := make([]rawWallet, 0) // return [] instead of nil if empty
	for _, wallet := range s.am.Wallets() {
		status, failure := wallet.Status()

		raw := rawWallet{
			URL:      wallet.URL().String(),
			Status:   status,
			Accounts: wallet.Accounts(),
		}
		if failure != nil {
			raw.Failure = failure.Error()
		}
		wallets = append(wallets, raw)
	}

	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(wallets); err != nil {
		return nil, err
	}
	return &pb.PrivateAccountAPIReply{
		RawWallets: &any.Any{
			Value: buf.Bytes(),
		},
	}, nil
}

// OpenWallet initiates a hardware wallet opening procedure, establishing a USB
// connection and attempting to authenticate via the provided passphrase. Note,
// the method may return an extra challenge requiring a second open (e.g. the
// Trezor PIN matrix challenge).
func (s *PrivateAccountAPIServer) OpenWallet(ctx context.Context, in *pb.PrivateAccountAPIRequest) (*pb.PrivateAccountAPIReply, error) {
	wallet, err := s.am.Wallet(in.Url.Value)
	if err != nil {
		return nil, err
	}
	pass := ""
	if in.Password != nil {
		pass = in.Password.Value
	}
	return nil, wallet.Open(pass)
}

// DeriveAccount requests a HD wallet to derive a new account, optionally pinning
// it for later reuse.
func (s *PrivateAccountAPIServer) DeriveAccount(ctx context.Context, in *pb.PrivateAccountAPIRequest) (*pb.PrivateAccountAPIReply, error) {
	wallet, err := s.am.Wallet(in.Url.Value)
	if err != nil {
		return nil, err
	}
	derivPath, err := accounts.ParseDerivationPath(in.Path.Value)
	if err != nil {
		return nil, err
	}
	if in.Pin == nil {
		in.Pin = new(wrappers.BoolValue)
	}
	account, err := wallet.Derive(derivPath, in.Pin.Value)
	if err != nil {
		return nil, err
	}

	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(&account); err != nil {
		return nil, err
	}
	return &pb.PrivateAccountAPIReply{
		Account: &any.Any{
			Value: buf.Bytes(),
		},
	}, nil
}

// NewAccount will create a new account and returns the address for the new account.
func (s *PrivateAccountAPIServer) NewAccount(ctx context.Context, in *pb.PrivateAccountAPIRequest) (*pb.PrivateAccountAPIReply, error) {
	acc, err := fetchKeystore(s.am).NewAccount(in.Password.Value)
	if err == nil {
		return &pb.PrivateAccountAPIReply{
			Address: acc.Address.Bytes(),
		}, nil
	}
	return nil, err
}

// ImportRawKey stores the given hex encoded ECDSA key into the key directory,
// encrypting it with the passphrase.
func (s *PrivateAccountAPIServer) ImportRawKey(ctx context.Context, in *pb.PrivateAccountAPIRequest) (*pb.PrivateAccountAPIReply, error) {
	key, err := crypto.HexToECDSA(in.PrivKey.Value)
	if err != nil {
		return &pb.PrivateAccountAPIReply{}, err
	}
	acc, err := fetchKeystore(s.am).ImportECDSA(key, in.Password.Value)
	return &pb.PrivateAccountAPIReply{
		Address: acc.Address.Bytes(),
	}, err
}

// UnlockAccount will unlock the account associated with the given address with
// the given password for duration seconds. If duration is nil it will use a
// default of 300 seconds. It returns an indication if the account was unlocked.
func (s *PrivateAccountAPIServer) UnlockAccount(ctx context.Context, in *pb.PrivateAccountAPIRequest) (reply *pb.PrivateAccountAPIReply, err error) {
	const max = uint64(time.Duration(math.MaxInt64) / time.Second)
	var d time.Duration
	if in.Duration == nil {
		d = 300 * time.Second
	} else if in.Duration.Value > max {
		return &pb.PrivateAccountAPIReply{
			IsOk: false,
		}, errors.New("unlock duration too large")
	} else {
		d = time.Duration(in.Duration.Value) * time.Second
	}
	err = fetchKeystore(s.am).TimedUnlock(accounts.Account{Address: common.BytesToAddress(in.Addr)}, in.Password.Value, d)
	return &pb.PrivateAccountAPIReply{
		IsOk: err == nil,
	}, err
}

// LockAccount will lock the account associated with the given address when it's unlocked.
func (s *PrivateAccountAPIServer) LockAccount(ctx context.Context, in *pb.PrivateAccountAPIRequest) (*pb.PrivateAccountAPIReply, error) {
	return &pb.PrivateAccountAPIReply{
		IsOk: fetchKeystore(s.am).Lock(common.BytesToAddress(in.Addr)) == nil,
	}, nil
}

// signTransactions sets defaults and signs the given transaction
// NOTE: the caller needs to ensure that the nonceLock is held, if applicable,
// and release it after the transaction has been submitted to the tx pool
func (s *PrivateAccountAPIServer) signTransaction(ctx context.Context, args SendTxArgs, passwd string) (*types.Transaction, error) {
	// Look up the wallet containing the requested signer
	account := accounts.Account{Address: args.From}
	wallet, err := s.am.Find(account)
	if err != nil {
		return nil, err
	}
	// Set some sanity defaults and terminate on failure
	if err := args.setDefaults(ctx, s.b); err != nil {
		return nil, err
	}
	// Assemble the transaction and sign with the wallet
	tx := args.toTransaction()

	var chainID *big.Int
	if config := s.b.ChainConfig(); config.IsEIP155(s.b.CurrentBlock().Number()) {
		chainID = config.ChainID
	}
	return wallet.SignTxWithPassphrase(account, passwd, tx, chainID)
}

// SendTransaction will create a transaction from the given arguments and
// tries to sign it with the key associated with args.To. If the given passwd isn't
// able to decrypt the key it fails.
func (s *PrivateAccountAPIServer) SendTransaction(ctx context.Context, in *pb.PrivateAccountAPIRequest) (*pb.PrivateAccountAPIReply, error) {
	buf := bytes.NewBuffer(in.SendTxArgs.Value)
	var args SendTxArgs
	dec := gob.NewDecoder(buf)
	if err := dec.Decode(&args); err != nil {
		return nil, err
	}
	if args.Nonce == nil {
		// Hold the addresse's mutex around signing to prevent concurrent assignment of
		// the same nonce to multiple accounts.
		s.nonceLock.LockAddr(args.From)
		defer s.nonceLock.UnlockAddr(args.From)
	}
	signed, err := s.signTransaction(ctx, args, in.Password.Value)
	if err != nil {
		return &pb.PrivateAccountAPIReply{}, err
	}

	txhash, err := submitTransaction(ctx, s.b, signed)
	if err != nil {
		return &pb.PrivateAccountAPIReply{}, err
	}

	return &pb.PrivateAccountAPIReply{
		TxHash: txhash.Bytes(),
	}, nil
}

// SignTransaction will create a transaction from the given arguments and
// tries to sign it with the key associated with args.To. If the given passwd isn't
// able to decrypt the key it fails. The transaction is returned in RLP-form, not broadcast
// to other nodes
func (s *PrivateAccountAPIServer) SignTransaction(ctx context.Context, in *pb.PrivateAccountAPIRequest) (*pb.PrivateAccountAPIReply, error) {
	buf := bytes.NewBuffer(in.SendTxArgs.Value)
	var args SendTxArgs
	dec := gob.NewDecoder(buf)
	if err := dec.Decode(&args); err != nil {
		return nil, err
	}
	// No need to obtain the noncelock mutex, since we won't be sending this
	// tx into the transaction pool, but right back to the user
	if args.Gas == nil {
		return nil, fmt.Errorf("gas not specified")
	}
	if args.GasPrice == nil {
		return nil, fmt.Errorf("gasPrice not specified")
	}
	if args.Nonce == nil {
		return nil, fmt.Errorf("nonce not specified")
	}
	signed, err := s.signTransaction(ctx, args, in.Password.Value)
	if err != nil {
		return nil, err
	}
	data, err := rlp.EncodeToBytes(signed)
	if err != nil {
		return nil, err
	}
	result := SignTransactionResult{data, signed}

	buf.Reset()
	enc := gob.NewEncoder(buf)
	if err := enc.Encode(&result); err != nil {
		return nil, err
	}
	return &pb.PrivateAccountAPIReply{
		SignTxResult: &any.Any{
			Value: buf.Bytes(),
		},
	}, nil
}

// Sign calculates an Ethereum ECDSA signature for:
// keccack256("\x19Ethereum Signed Message:\n" + len(message) + message))
//
// Note, the produced signature conforms to the secp256k1 curve R, S and V values,
// where the V value will be 27 or 28 for legacy reasons.
//
// The key used to calculate the signature is decrypted with the given password.
//
// https://github.com/ethereum/go-ethereum/wiki/Management-APIServers#personal_sign
func (s *PrivateAccountAPIServer) Sign(ctx context.Context, in *pb.PrivateAccountAPIRequest) (*pb.PrivateAccountAPIReply, error) {
	// Look up the wallet containing the requested signer
	account := accounts.Account{Address: common.BytesToAddress(in.Addr)}

	wallet, err := s.b.AccountManager().Find(account)
	if err != nil {
		return nil, err
	}
	// Assemble sign the data with the wallet
	signature, err := wallet.SignHashWithPassphrase(account, in.Password.Value, signHash(in.Data))
	if err != nil {
		return nil, err
	}
	signature[64] += 27 // Transform V from 0/1 to 27/28 according to the yellow paper
	return &pb.PrivateAccountAPIReply{
		Signature: signature,
	}, nil
}

// EcRecover returns the address for the account that was used to create the signature.
// Note, this function is compatible with eth_sign and personal_sign. As such it recovers
// the address of:
// hash = keccak256("\x19Ethereum Signed Message:\n"${message length}${message})
// addr = ecrecover(hash, signature)
//
// Note, the signature must conform to the secp256k1 curve R, S and V values, where
// the V value must be be 27 or 28 for legacy reasons.
//
// https://github.com/ethereum/go-ethereum/wiki/Management-APIServers#personal_ecRecover
func (s *PrivateAccountAPIServer) EcRecover(ctx context.Context, in *pb.PrivateAccountAPIRequest) (*pb.PrivateAccountAPIReply, error) {
	if len(in.Sig) != 65 {
		return nil, fmt.Errorf("signature must be 65 bytes long")
	}
	if in.Sig[64] != 27 && in.Sig[64] != 28 {
		return nil, fmt.Errorf("invalid Ethereum signature (V is not 27 or 28)")
	}
	in.Sig[64] -= 27 // Transform yellow paper V from 27/28 to 0/1

	rpk, err := crypto.SigToPub(signHash(in.Data), in.Sig)
	if err != nil {
		return nil, err
	}
	return &pb.PrivateAccountAPIReply{
		Address: crypto.PubkeyToAddress(*rpk).Bytes(),
	}, nil
}

// SignAndSendTransaction was renamed to SendTransaction. This method is deprecated
// and will be removed in the future. It primary goal is to give clients time to update.
func (s *PrivateAccountAPIServer) SignAndSendTransaction(ctx context.Context, in *pb.PrivateAccountAPIRequest) (*pb.PrivateAccountAPIReply, error) {
	return s.SendTransaction(ctx, in)
}

// PublicBlockChainAPIServer provides an APIServer to access the Ethereum blockchain.
// It offers only methods that operate on public data that is freely available to anyone.
type PublicBlockChainAPIServer struct {
	b Backend
}

// NewPublicBlockChainAPIServer creates a new Ethereum blockchain APIServer.
func NewPublicBlockChainAPIServer(b Backend) *PublicBlockChainAPIServer {
	return &PublicBlockChainAPIServer{b}
}

func (api *PublicBlockChainAPIServer) RegisterServer(s *grpc.Server) {
	pb.RegisterPublicBlockChainAPIServer(s, api)
}

func (api *PublicBlockChainAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	pb.RegisterPublicBlockChainAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// BlockNumber returns the block number of the chain head.
func (s *PublicBlockChainAPIServer) BlockNumber(ctx context.Context, in *empty.Empty) (reply *pb.PublicBlockChainAPIReply, err error) {
	header, _ := s.b.HeaderByNumber(context.Background(), rpc.LatestBlockNumber) // latest header should always be available
	return &pb.PublicBlockChainAPIReply{
		BlockNumber: header.Number.Uint64(),
	}, nil
}

// GetBalance returns the amount of wei for the given address in the state of the
// given block number. The rpc.LatestBlockNumber and rpc.PendingBlockNumber meta
// block numbers are also allowed.
func (s *PublicBlockChainAPIServer) GetBalance(ctx context.Context, in *pb.PublicBlockChainAPIRequest) (*pb.PublicBlockChainAPIReply, error) {
	state, _, err := s.b.StateAndHeaderByNumber(ctx, rpc.BlockNumber(in.BlockNumber), false)
	if state == nil || err != nil {
		return nil, err
	}
	return &pb.PublicBlockChainAPIReply{
		Balance: state.GetBalance(common.BytesToAddress(in.Address)).Bytes(),
	}, state.Error()
}

// rpcOutputBlock uses the generalized output filler, then adds the total difficulty field, which requires
// a `PublicBlockchainAPI`.
func (s *PublicBlockChainAPIServer) rpcOutputBlock(b *types.Block, inclTx bool, fullTx bool) (map[string]interface{}, error) {
	fields, err := RPCMarshalBlock(b, inclTx, fullTx)
	if err != nil {
		return nil, err
	}
	fields["totalDifficulty"] = (*hexutil.Big)(s.b.GetTd(b.Hash()))
	return fields, err
}

// GetBlockByNumber returns the requested block. When blockNr is -1 the chain head is returned. When fullTx is true all
// transactions in the block are returned in full detail, otherwise only the transaction hash is returned.
func (s *PublicBlockChainAPIServer) GetBlockByNumber(ctx context.Context, in *pb.PublicBlockChainAPIRequest) (*pb.PublicBlockChainAPIReply, error) {
	block, err := s.b.BlockByNumber(ctx, rpc.BlockNumber(in.BlockNumber))
	if block != nil {
		response, err := s.rpcOutputBlock(block, true, in.FullTx)
		if err == nil && rpc.BlockNumber(in.BlockNumber) == rpc.PendingBlockNumber {
			// Pending blocks need to nil out a few fields
			for _, field := range []string{"hash", "nonce", "miner"} {
				response[field] = nil
			}
		}
		var buf bytes.Buffer
		enc := gob.NewEncoder(&buf)
		if err := enc.Encode(response); err != nil {
			return nil, err
		}

		return &pb.PublicBlockChainAPIReply{
			BlockInfo: &any.Any{
				Value: buf.Bytes(),
			},
		}, nil
	}
	return nil, err
}

// GetBlockByHash returns the requested block. When fullTx is true all transactions in the block are returned in full
// detail, otherwise only the transaction hash is returned.
func (s *PublicBlockChainAPIServer) GetBlockByHash(ctx context.Context, in *pb.PublicBlockChainAPIRequest) (*pb.PublicBlockChainAPIReply, error) {
	block, err := s.b.GetBlock(ctx, common.BytesToHash(in.BlockHash))
	if block != nil {
		blockInfo, err := s.rpcOutputBlock(block, true, in.FullTx)
		if err != nil {
			return nil, err
		}
		var buf bytes.Buffer
		enc := gob.NewEncoder(&buf)
		if err := enc.Encode(&blockInfo); err != nil {
			return nil, err
		}
		return &pb.PublicBlockChainAPIReply{
			BlockInfo: &any.Any{
				Value: buf.Bytes(),
			},
		}, nil
	}
	return nil, err
}

// GetUncleByBlockNumberAndIndex returns the uncle block for the given block hash and index. When fullTx is true
// all transactions in the block are returned in full detail, otherwise only the transaction hash is returned.
func (s *PublicBlockChainAPIServer) GetUncleByBlockNumberAndIndex(ctx context.Context, in *pb.PublicBlockChainAPIRequest) (*pb.PublicBlockChainAPIReply, error) {
	// No uncles for dpor
	// return map[string]interface{}{}, nil
	return nil, nil
}

// GetUncleByBlockHashAndIndex returns the uncle block for the given block hash and index. When fullTx is true
// all transactions in the block are returned in full detail, otherwise only the transaction hash is returned.
func (s *PublicBlockChainAPIServer) GetUncleByBlockHashAndIndex(ctx context.Context, in *pb.PublicBlockChainAPIRequest) (*pb.PublicBlockChainAPIReply, error) {
	// No uncles for dpor
	// return map[string]interface{}{}, nil
	return nil, nil
}

// GetUncleCountByBlockNumber returns number of uncles in the block for the given block number
func (s *PublicBlockChainAPIServer) GetUncleCountByBlockNumber(ctx context.Context, in *pb.PublicBlockChainAPIRequest) (*pb.PublicBlockChainAPIReply, error) {
	// No uncles for dpor
	return &pb.PublicBlockChainAPIReply{
		UncleCount: 0,
	}, nil
}

// GetUncleCountByBlockHash returns number of uncles in the block for the given block hash
func (s *PublicBlockChainAPIServer) GetUncleCountByBlockHash(ctx context.Context, in *pb.PublicBlockChainAPIRequest) (*pb.PublicBlockChainAPIReply, error) {
	// No uncles for dpor
	return &pb.PublicBlockChainAPIReply{
		UncleCount: 0,
	}, nil
}

// GetCode returns the code stored at the given address in the state for the given block number.
func (s *PublicBlockChainAPIServer) GetCode(ctx context.Context, in *pb.PublicBlockChainAPIRequest) (*pb.PublicBlockChainAPIReply, error) {
	state, _, err := s.b.StateAndHeaderByNumber(ctx, rpc.BlockNumber(in.BlockNumber), false)
	if state == nil || err != nil {
		return nil, err
	}
	code := state.GetCode(common.BytesToAddress(in.Address))
	return &pb.PublicBlockChainAPIReply{
		Code: code,
	}, state.Error()
}

// GetStorageAt returns the storage from the state at the given address, key and
// block number. The rpc.LatestBlockNumber and rpc.PendingBlockNumber meta block
// numbers are also allowed.
func (s *PublicBlockChainAPIServer) GetStorageAt(ctx context.Context, in *pb.PublicBlockChainAPIRequest) (*pb.PublicBlockChainAPIReply, error) {
	state, _, err := s.b.StateAndHeaderByNumber(ctx, rpc.BlockNumber(in.BlockNumber), false)
	if state == nil || err != nil {
		return nil, err
	}
	res := state.GetState(common.BytesToAddress(in.Address), common.HexToHash(in.Key))
	return &pb.PublicBlockChainAPIReply{
		Storage: res[:],
	}, state.Error()
}

func (s *PublicBlockChainAPIServer) doCall(ctx context.Context, args CallArgs, blockNr rpc.BlockNumber, vmCfg vm.Config, timeout time.Duration) ([]byte, uint64, bool, error) {
	defer func(start time.Time) { log.Debug("Executing EVM call finished", "runtime", time.Since(start)) }(time.Now())
	state, header, err := s.b.StateAndHeaderByNumber(ctx, blockNr, args.IsPrivate)

	if state == nil || err != nil {
		return nil, 0, false, err
	}
	// Set sender address or use a default if none specified
	addr := args.From
	if addr == (common.Address{}) {
		if wallets := s.b.AccountManager().Wallets(); len(wallets) > 0 {
			if accounts := wallets[0].Accounts(); len(accounts) > 0 {
				addr = accounts[0].Address
			}
		}
	}
	// Set default gas & gas price if none were set
	gas, gasPrice := uint64(args.Gas), args.GasPrice.ToInt()
	if gas == 0 {
		gas = math.MaxUint64 / 2
	}
	if gasPrice.Sign() == 0 {
		gasPrice = new(big.Int).SetUint64(defaultGasPrice)
	}

	// Create new call message
	msg := types.NewMessage(addr, args.To, 0, args.Value.ToInt(), gas, gasPrice, args.Data, false)

	// Setup context so it may be cancelled the call has completed
	// or, in case of unmetered gas, setup a context with a timeout.
	var cancel context.CancelFunc
	if timeout > 0 {
		ctx, cancel = context.WithTimeout(ctx, timeout)
	} else {
		ctx, cancel = context.WithCancel(ctx)
	}
	// Make sure the context is cancelled when the call has completed
	// this makes sure resources are cleaned up.
	defer cancel()

	// Get a new instance of the EVM.
	evm, vmError, err := s.b.GetEVM(ctx, msg, state, header, vmCfg)
	if err != nil {
		return nil, 0, false, err
	}
	// Wait for the context to be done and cancel the evm. Even if the
	// EVM has finished, cancelling may be done (repeatedly)
	go func() {
		<-ctx.Done()
		evm.Cancel()
	}()

	// Setup the gas pool (also for unmetered requests)
	// and apply the message.
	gp := new(core.GasPool).AddGas(math.MaxUint64)
	res, gas, failed, err := core.ApplyMessage(evm, msg, gp)
	if err := vmError(); err != nil {
		return nil, 0, false, err
	}

	return res, gas, failed, err
}

// Call executes the given transaction on the state for the given block number.
// It doesn't make and changes in the state/blockchain and is useful to execute and retrieve values.
func (s *PublicBlockChainAPIServer) Call(ctx context.Context, in *pb.PublicBlockChainAPIRequest) (*pb.PublicBlockChainAPIReply, error) {
	buf := bytes.NewBuffer(in.Args.Value)
	dec := gob.NewDecoder(buf)
	var args CallArgs
	if err := dec.Decode(&args); err != nil {
		return nil, err
	}
	result, _, _, err := s.doCall(ctx, args, rpc.BlockNumber(in.BlockNumber), vm.Config{}, 5*time.Second)
	return &pb.PublicBlockChainAPIReply{
		Result: result,
	}, err
}

// EstimateGas returns an estimate of the amount of gas needed to execute the
// given transaction against the current pending block.
func (s *PublicBlockChainAPIServer) EstimateGas(ctx context.Context, in *pb.PublicBlockChainAPIRequest) (*pb.PublicBlockChainAPIReply, error) {
	buf := bytes.NewBuffer(in.Args.Value)
	dec := gob.NewDecoder(buf)
	var args CallArgs
	if err := dec.Decode(&args); err != nil {
		return nil, err
	}
	// Binary search the gas requirement, as it may be higher than the amount used
	var (
		lo  uint64 = configs.TxGas - 1
		hi  uint64
		cap uint64
	)
	if uint64(args.Gas) >= configs.TxGas {
		hi = uint64(args.Gas)
	} else {
		// Retrieve the current pending block to act as the gas ceiling
		block, err := s.b.BlockByNumber(ctx, rpc.PendingBlockNumber)
		if err != nil {
			return nil, err
		}
		hi = block.GasLimit()
	}
	cap = hi

	// Create a helper to check if a gas allowance results in an executable transaction
	executable := func(gas uint64) bool {
		args.Gas = hexutil.Uint64(gas)

		_, _, failed, err := s.doCall(ctx, args, rpc.PendingBlockNumber, vm.Config{}, 0)
		if err != nil || failed {
			return false
		}
		return true
	}
	// Execute the binary search and hone in on an executable gas limit
	for lo+1 < hi {
		mid := (hi + lo) / 2
		if !executable(mid) {
			lo = mid
		} else {
			hi = mid
		}
	}
	// Reject the transaction as invalid if it still fails at the highest allowance
	if hi == cap {
		if !executable(hi) {
			return nil, fmt.Errorf("gas required exceeds allowance or always failing transaction")
		}
	}
	return &pb.PublicBlockChainAPIReply{
		EstimateGas: hi,
	}, nil
}

// PublicTransactionPoolAPIServer exposes methods for the RPC interface
type PublicTransactionPoolAPIServer struct {
	b         Backend
	nonceLock *AddrLocker
}

// NewPublicTransactionPoolAPIServer creates a new RPC service with methods specific for the transaction pool.
func NewPublicTransactionPoolAPIServer(b Backend, nonceLock *AddrLocker) *PublicTransactionPoolAPIServer {
	return &PublicTransactionPoolAPIServer{b, nonceLock}
}

func (api *PublicTransactionPoolAPIServer) RegisterServer(s *grpc.Server) {
	pb.RegisterPublicTransactionPoolAPIServer(s, api)
}

func (api *PublicTransactionPoolAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	pb.RegisterPublicTransactionPoolAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// GetBlockTransactionCountByNumber returns the number of transactions in the block with the given block number.
func (s *PublicTransactionPoolAPIServer) GetBlockTransactionCountByNumber(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	if block, _ := s.b.BlockByNumber(ctx, rpc.BlockNumber(in.BlockNumber)); block != nil {
		return &pb.PublicTransactionPoolAPIReply{
			Count: uint64(len(block.Transactions())),
		}, nil
	}
	return nil, nil
}

// GetBlockTransactionCountByHash returns the number of transactions in the block with the given hash.
func (s *PublicTransactionPoolAPIServer) GetBlockTransactionCountByHash(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	if block, _ := s.b.GetBlock(ctx, common.BytesToHash(in.BlockHash)); block != nil {
		return &pb.PublicTransactionPoolAPIReply{
			Count: uint64(len(block.Transactions())),
		}, nil
	}
	return nil, nil
}

// GetTransactionByBlockNumberAndIndex returns the transaction for the given block number and index.
func (s *PublicTransactionPoolAPIServer) GetTransactionByBlockNumberAndIndex(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	if block, _ := s.b.BlockByNumber(ctx, rpc.BlockNumber(in.BlockNumber)); block != nil {
		rpcTx := newRPCTransactionFromBlockIndex(block, in.Index)
		var buf bytes.Buffer
		enc := gob.NewEncoder(&buf)
		if err := enc.Encode(&rpcTx); err != nil {
			return nil, err
		}
		return &pb.PublicTransactionPoolAPIReply{
			RpcTransaction: &any.Any{
				Value: buf.Bytes(),
			},
		}, nil
	}
	return nil, nil
}

// GetTransactionByBlockHashAndIndex returns the transaction for the given block hash and index.
func (s *PublicTransactionPoolAPIServer) GetTransactionByBlockHashAndIndex(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	if block, _ := s.b.GetBlock(ctx, common.BytesToHash(in.BlockHash)); block != nil {
		rpcTx := newRPCTransactionFromBlockIndex(block, in.Index)
		var buf bytes.Buffer
		enc := gob.NewEncoder(&buf)
		if err := enc.Encode(&rpcTx); err != nil {
			return nil, err
		}
		return &pb.PublicTransactionPoolAPIReply{
			RpcTransaction: &any.Any{
				Value: buf.Bytes(),
			},
		}, nil
	}
	return nil, nil
}

// GetRawTransactionByBlockNumberAndIndex returns the bytes of the transaction for the given block number and index.
func (s *PublicTransactionPoolAPIServer) GetRawTransactionByBlockNumberAndIndex(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	if block, _ := s.b.BlockByNumber(ctx, rpc.BlockNumber(in.BlockNumber)); block != nil {
		rpcTx := newRPCTransactionFromBlockIndex(block, in.Index)
		var buf bytes.Buffer
		enc := gob.NewEncoder(&buf)
		if err := enc.Encode(&rpcTx); err != nil {
			return nil, err
		}
		return &pb.PublicTransactionPoolAPIReply{
			RpcTransaction: &any.Any{
				Value: buf.Bytes(),
			},
		}, nil
	}
	return nil, nil
}

// GetRawTransactionByBlockHashAndIndex returns the bytes of the transaction for the given block hash and index.
func (s *PublicTransactionPoolAPIServer) GetRawTransactionByBlockHashAndIndex(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	if block, _ := s.b.GetBlock(ctx, common.BytesToHash(in.BlockHash)); block != nil {
		rpcTx := newRPCTransactionFromBlockIndex(block, in.Index)
		var buf bytes.Buffer
		enc := gob.NewEncoder(&buf)
		if err := enc.Encode(&rpcTx); err != nil {
			return nil, err
		}
		return &pb.PublicTransactionPoolAPIReply{
			RpcTransaction: &any.Any{
				Value: buf.Bytes(),
			},
		}, nil
	}
	return nil, nil
}

// GetTransactionCount returns the number of transactions the given address has sent for the given block number
func (s *PublicTransactionPoolAPIServer) GetTransactionCount(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	state, _, err := s.b.StateAndHeaderByNumber(ctx, rpc.BlockNumber(in.BlockNumber), false)
	if state == nil || err != nil {
		return nil, err
	}
	nonce := state.GetNonce(common.BytesToAddress(in.Address))
	return &pb.PublicTransactionPoolAPIReply{
		Count: nonce,
	}, state.Error()
}

// GetTransactionByHash returns the transaction for the given hash
func (s *PublicTransactionPoolAPIServer) GetTransactionByHash(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	// Try to return an already finalized transaction
	if tx, blockHash, blockNumber, index := rawdb.ReadTransaction(s.b.ChainDb(), common.BytesToHash(in.TxHash)); tx != nil {
		rpcTx := newRPCTransaction(tx, blockHash, blockNumber, index)
		var buf bytes.Buffer
		enc := gob.NewEncoder(&buf)
		if err := enc.Encode(&rpcTx); err != nil {
			return nil, err
		}
		return &pb.PublicTransactionPoolAPIReply{
			RpcTransaction: &any.Any{
				Value: buf.Bytes(),
			},
		}, nil
	}
	// No finalized transaction, try to retrieve it from the pool
	if tx := s.b.GetPoolTransaction(common.BytesToHash(in.BlockHash)); tx != nil {
		var buf bytes.Buffer
		enc := gob.NewEncoder(&buf)
		if err := enc.Encode(&tx); err != nil {
			return nil, err
		}
		return &pb.PublicTransactionPoolAPIReply{
			RpcTransaction: &any.Any{
				Value: buf.Bytes(),
			},
		}, nil
	}
	// Transaction unknown, return as such
	return nil, nil
}

// GetRawTransactionByHash returns the bytes of the transaction for the given hash.
func (s *PublicTransactionPoolAPIServer) GetRawTransactionByHash(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	var tx *types.Transaction

	// Retrieve a finalized transaction, or a pooled otherwise
	if tx, _, _, _ = rawdb.ReadTransaction(s.b.ChainDb(), common.BytesToHash(in.TxHash)); tx == nil {
		if tx = s.b.GetPoolTransaction(common.BytesToHash(in.TxHash)); tx == nil {
			// Transaction not found anywhere, abort
			return nil, nil
		}
	}
	txBytes, err := rlp.EncodeToBytes(tx)
	if err != nil {
		return nil, err
	}
	// Serialize to RLP and return
	return &pb.PublicTransactionPoolAPIReply{
		TxBytes: txBytes,
	}, nil
}

// GetTransactionReceipt returns the transaction receipt for the given transaction hash.
func (s *PublicTransactionPoolAPIServer) GetTransactionReceipt(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	tx, blockHash, blockNumber, index := rawdb.ReadTransaction(s.b.ChainDb(), common.BytesToHash(in.TxHash))
	if tx == nil {
		return nil, nil
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

	fields := map[string]interface{}{
		"blockHash":         blockHash,
		"blockNumber":       hexutil.Uint64(blockNumber),
		"transactionHash":   common.BytesToHash(in.TxHash),
		"transactionIndex":  hexutil.Uint64(index),
		"from":              from,
		"to":                tx.To(),
		"gasUsed":           hexutil.Uint64(receipt.GasUsed),
		"cumulativeGasUsed": hexutil.Uint64(receipt.CumulativeGasUsed),
		"contractAddress":   nil,
		"logs":              receipt.Logs,
		"logsBloom":         receipt.Bloom,
	}

	// Assign receipt status or post state.
	if len(receipt.PostState) > 0 {
		fields["root"] = hexutil.Bytes(receipt.PostState)
	} else {
		fields["status"] = hexutil.Uint(receipt.Status)
	}
	if receipt.Logs == nil {
		fields["logs"] = [][]*types.Log{}
	}
	// If the ContractAddress is 20 0x0 bytes, assume it is not a contract creation
	if receipt.ContractAddress != (common.Address{}) {
		fields["contractAddress"] = receipt.ContractAddress
	}
	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode(fields); err != nil {
		return nil, err
	}

	return &pb.PublicTransactionPoolAPIReply{
		Fields: &any.Any{
			Value: buf.Bytes(),
		},
	}, nil
}

// sign is a helper function that signs a transaction with the private key of the given address.
func (s *PublicTransactionPoolAPIServer) sign(addr common.Address, tx *types.Transaction) (*types.Transaction, error) {
	// Look up the wallet containing the requested signer
	account := accounts.Account{Address: addr}

	wallet, err := s.b.AccountManager().Find(account)
	if err != nil {
		return nil, err
	}
	// Request the wallet to sign the transaction
	var chainID *big.Int
	if config := s.b.ChainConfig(); config.IsEIP155(s.b.CurrentBlock().Number()) {
		chainID = config.ChainID
	}
	return wallet.SignTx(account, tx, chainID)
}

func (s *PublicTransactionPoolAPIServer) SendTransaction(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	var args SendTxArgs
	buf := bytes.NewBuffer(in.SendTxArgs.Value)
	dec := gob.NewDecoder(buf)
	if err := dec.Decode(&args); err != nil {
		return nil, err
	}
	// Look up the wallet containing the requested signer
	account := accounts.Account{Address: args.From}

	wallet, err := s.b.AccountManager().Find(account)
	if err != nil {
		return nil, err
	}

	if args.Nonce == nil {
		// Hold the addresse's mutex around signing to prevent concurrent assignment of
		// the same nonce to multiple accounts.
		s.nonceLock.LockAddr(args.From)
		defer s.nonceLock.UnlockAddr(args.From)
	}

	// Set some sanity defaults and terminate on failure
	if err := args.setDefaults(ctx, s.b); err != nil {
		return nil, err
	}

	if args.IsPrivate {
		// If args.Data is nil, it must be the transaction of transferring tokens, that should be always public.
		if len(args.Participants) == 0 || args.Data == nil {
			return nil, InvalidPrivateTxErr

		}

		payloadReplace, err := private.SealPrivatePayload(([]byte)(*args.Data), (uint64)(*args.Nonce), args.Participants, s.b.RemoteDB())
		if err != nil {
			return nil, err
		}

		// Replace original content with security one.
		replaceData, _ := rlp.EncodeToBytes(payloadReplace)
		args.Data = (*hexutil.Bytes)(&replaceData)
	}

	// Assemble the transaction and sign with the wallet
	tx := args.toTransaction()

	var chainID *big.Int
	if config := s.b.ChainConfig(); config.IsEIP155(s.b.CurrentBlock().Number()) || config.IsCpchain() {
		chainID = config.ChainID
	}
	signed, err := wallet.SignTx(account, tx, chainID)
	if err != nil {
		return nil, err
	}
	hash, err := submitTransaction(ctx, s.b, signed)
	if err != nil {
		return nil, err
	}

	return &pb.PublicTransactionPoolAPIReply{
		TxHash: hash.Bytes(),
	}, nil
}

// SendRawTransaction will add the signed transaction to the transaction pool.
// The sender is responsible for signing the transaction and using the correct nonce.
func (s *PublicTransactionPoolAPIServer) SendRawTransaction(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	tx := new(types.Transaction)
	if err := rlp.DecodeBytes(hexutil.Bytes(in.EncodedTx), tx); err != nil {
		return nil, err
	}
	hash, err := submitTransaction(ctx, s.b, tx)
	if err != nil {
		return nil, err
	}

	return &pb.PublicTransactionPoolAPIReply{
		TxHash: hash.Bytes(),
	}, nil
}

// Sign calculates an ECDSA signature for:
// keccack256("\x19Ethereum Signed Message:\n" + len(message) + message).
//
// Note, the produced signature conforms to the secp256k1 curve R, S and V values,
// where the V value will be 27 or 28 for legacy reasons.
//
// The account associated with addr must be unlocked.
//
// https://github.com/ethereum/wiki/wiki/JSON-RPC#eth_sign
func (s *PublicTransactionPoolAPIServer) Sign(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	// Look up the wallet containing the requested signer
	account := accounts.Account{Address: common.BytesToAddress(in.Address)}

	wallet, err := s.b.AccountManager().Find(account)
	if err != nil {
		return nil, err
	}
	// Sign the requested hash with the wallet
	signature, err := wallet.SignHash(account, signHash(hexutil.Bytes(in.Payload)))
	if err == nil {
		signature[64] += 27 // Transform V from 0/1 to 27/28 according to the yellow paper
	}
	return &pb.PublicTransactionPoolAPIReply{
		Signature: signature,
	}, nil
}

// SignTransaction will sign the given transaction with the from account.
// The node needs to have the private key of the account corresponding with
// the given from address and it needs to be unlocked.
func (s *PublicTransactionPoolAPIServer) SignTransaction(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	buf := bytes.NewBuffer(in.SendTxArgs.Value)
	dec := gob.NewDecoder(buf)
	var args SendTxArgs
	if err := dec.Decode(&args); err != nil {
		return nil, err
	}
	if args.Gas == nil {
		return nil, fmt.Errorf("gas not specified")
	}
	if args.GasPrice == nil {
		return nil, fmt.Errorf("gasPrice not specified")
	}
	if args.Nonce == nil {
		return nil, fmt.Errorf("nonce not specified")
	}
	if err := args.setDefaults(ctx, s.b); err != nil {
		return nil, err
	}
	tx, err := s.sign(args.From, args.toTransaction())
	if err != nil {
		return nil, err
	}
	data, err := rlp.EncodeToBytes(tx)
	if err != nil {
		return nil, err
	}
	enc := gob.NewEncoder(buf)
	if err = enc.Encode(&SignTransactionResult{data, tx}); err != nil {
		return nil, err
	}

	return &pb.PublicTransactionPoolAPIReply{
		SignTxResult: &any.Any{
			Value: buf.Bytes(),
		},
	}, nil
}

// PendingTransactions returns the transactions that are in the transaction pool
// and have a from address that is one of the accounts this node manages.
func (s *PublicTransactionPoolAPIServer) PendingTransactions(ctx context.Context, in *empty.Empty) (*pb.PublicTransactionPoolAPIReply, error) {
	pending, err := s.b.GetPoolTransactions()
	if err != nil {
		return nil, err
	}
	accounts := make(map[common.Address]struct{})
	for _, wallet := range s.b.AccountManager().Wallets() {
		for _, account := range wallet.Accounts() {
			accounts[account.Address] = struct{}{}
		}
	}
	transactions := make([]*RPCTransaction, 0, len(pending))
	for _, tx := range pending {
		var signer types.Signer = types.HomesteadSigner{}
		if tx.Protected() {
			signer = types.NewPrivTxSupportEIP155Signer(tx.ChainId())
		}
		from, _ := types.Sender(signer, tx)
		if _, exists := accounts[from]; exists {
			transactions = append(transactions, newRPCPendingTransaction(tx))
		}
	}

	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	if err := enc.Encode((transactions)); err != nil {
		return nil, err
	}

	return &pb.PublicTransactionPoolAPIReply{
		PendingTxs: &any.Any{
			Value: buf.Bytes(),
		},
	}, nil
}

// Resend accepts an existing transaction and a new gas price and limit. It will remove
// the given transaction from the pool and reinsert it with the new gas price and limit.
func (s *PublicTransactionPoolAPIServer) Resend(ctx context.Context, in *pb.PublicTransactionPoolAPIRequest) (*pb.PublicTransactionPoolAPIReply, error) {
	buf := bytes.NewBuffer(in.SendTxArgs.Value)
	dec := gob.NewDecoder(buf)
	var sendArgs SendTxArgs
	if err := dec.Decode(&sendArgs); err != nil {
		return nil, err
	}
	if sendArgs.Nonce == nil {
		return nil, fmt.Errorf("missing transaction nonce in transaction spec")
	}
	if err := sendArgs.setDefaults(ctx, s.b); err != nil {
		return nil, err
	}
	matchTx := sendArgs.toTransaction()
	pending, err := s.b.GetPoolTransactions()
	if err != nil {
		return nil, err
	}

	for _, p := range pending {
		var signer types.Signer = types.HomesteadSigner{}
		if p.Protected() {
			signer = types.NewPrivTxSupportEIP155Signer(p.ChainId())
		}
		wantSigHash := signer.Hash(matchTx)

		if pFrom, err := types.Sender(signer, p); err == nil && pFrom == sendArgs.From && signer.Hash(p) == wantSigHash {
			// Match. Re-sign and send the transaction.
			var gasPrice *hexutil.Big
			buf := bytes.NewBuffer(in.GasPrice)
			dec := gob.NewDecoder(buf)
			if err := dec.Decode(gasPrice); err != nil {
				return nil, err
			}
			if gasPrice != nil && (*big.Int)(gasPrice).Sign() != 0 {
				sendArgs.GasPrice = gasPrice
			}
			if in.GasLimit != nil && in.GasLimit.Value != 0 {
				sendArgs.Gas = (*hexutil.Uint64)(&in.GasLimit.Value)
			}
			signedTx, err := s.sign(sendArgs.From, sendArgs.toTransaction())
			if err != nil {
				return nil, err
			}
			if err = s.b.SendTx(ctx, signedTx); err != nil {
				return nil, err
			}
			return &pb.PublicTransactionPoolAPIReply{
				TxHash: signedTx.Hash().Bytes(),
			}, nil
		}
	}

	return nil, fmt.Errorf("Transaction %#x not found", matchTx.Hash())
}

// PublicDebugAPIServer is the collection of Ethereum APIServers exposed over the public
// debugging endpoint.
type PublicDebugAPIServer struct {
	b Backend
}

// NewPublicDebugAPIServer creates a new APIServer definition for the public debug methods
// of the Ethereum service.
func NewPublicDebugAPIServer(b Backend) *PublicDebugAPIServer {
	return &PublicDebugAPIServer{b: b}
}

func (api *PublicDebugAPIServer) RegisterServer(s *grpc.Server) {
	pb.RegisterPublicDebugAPIServer(s, api)
}

func (api *PublicDebugAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	pb.RegisterPublicDebugAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// GetBlockRlp retrieves the RLP encoded for of a single block.
func (api *PublicDebugAPIServer) GetBlockRlp(ctx context.Context, in *pb.PublicDebugAPIRequest) (*pb.PublicDebugAPIReply, error) {
	block, _ := api.b.BlockByNumber(ctx, rpc.BlockNumber(in.BlockNumber))
	if block == nil {
		return nil, fmt.Errorf("block #%d not found", in.BlockNumber)
	}
	encoded, err := rlp.EncodeToBytes(block)
	if err != nil {
		return nil, err
	}
	return &pb.PublicDebugAPIReply{
		Rlp: fmt.Sprintf("%x", encoded),
	}, nil
}

// PrintBlock retrieves a block and returns its pretty printed form.
func (api *PublicDebugAPIServer) PrintBlock(ctx context.Context, in *pb.PublicDebugAPIRequest) (*pb.PublicDebugAPIReply, error) {
	block, _ := api.b.BlockByNumber(ctx, rpc.BlockNumber(in.BlockNumber))
	if block == nil {
		return nil, fmt.Errorf("block #%d not found", in.BlockNumber)
	}
	return &pb.PublicDebugAPIReply{
		Info: spew.Sdump(block),
	}, nil
}

// SeedHash retrieves the seed hash of a block.
func (api *PublicDebugAPIServer) SeedHash(ctx context.Context, in *pb.PublicDebugAPIRequest) (*pb.PublicDebugAPIReply, error) {
	block, _ := api.b.BlockByNumber(ctx, rpc.BlockNumber(in.BlockNumber))
	if block == nil {
		return nil, fmt.Errorf("block #%d not found", in.BlockNumber)
	}
	return &pb.PublicDebugAPIReply{
		Info: fmt.Sprintf("0x%x", ethash.SeedHash(in.BlockNumber)),
	}, nil
}

// PrivateDebugAPIServer is the collection of Ethereum APIServers exposed over the private
// debugging endpoint.
type PrivateDebugAPIServer struct {
	b Backend
}

// NewPrivateDebugAPIServer creates a new APIServer definition for the private debug methods
// of the Ethereum service.
func NewPrivateDebugAPIServer(b Backend) *PrivateDebugAPIServer {
	return &PrivateDebugAPIServer{b: b}
}

func (api *PrivateDebugAPIServer) RegisterServer(s *grpc.Server) {
	pb.RegisterPrivateDebugAPIServer(s, api)
}

func (api *PrivateDebugAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	pb.RegisterPrivateDebugAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// ChaindbProperty returns leveldb properties of the chain database.
func (api *PrivateDebugAPIServer) ChaindbProperty(ctx context.Context, in *pb.PrivateDebugAPIRequest) (*pb.PrivateDebugAPIReply, error) {
	ldb, ok := api.b.ChainDb().(interface {
		LDB() *leveldb.DB
	})
	if !ok {
		return nil, fmt.Errorf("chaindbProperty does not work for memory databases")
	}
	if in.Property == "" {
		in.Property = "leveldb.stats"
	} else if !strings.HasPrefix(in.Property, "leveldb.") {
		in.Property = "leveldb." + in.Property
	}
	property, err := ldb.LDB().GetProperty(in.Property)
	if err != nil {
		return nil, err
	}

	return &pb.PrivateDebugAPIReply{
		Property: property,
	}, nil
}

func (api *PrivateDebugAPIServer) ChaindbCompact(ctx context.Context, in *empty.Empty) (*pb.PrivateDebugAPIReply, error) {
	ldb, ok := api.b.ChainDb().(interface {
		LDB() *leveldb.DB
	})
	if !ok {
		return nil, fmt.Errorf("chaindbCompact does not work for memory databases")
	}
	for b := byte(0); b < 255; b++ {
		log.Info("Compacting chain database", "range", fmt.Sprintf("0x%0.2X-0x%0.2X", b, b+1))
		err := ldb.LDB().CompactRange(util.Range{Start: []byte{b}, Limit: []byte{b + 1}})
		if err != nil {
			log.Error("Database compaction failed", "err", err)
			return nil, err
		}
	}
	return nil, nil
}

// SetHead rewinds the head of the blockchain to a previous block.
func (api *PrivateDebugAPIServer) SetHead(ctx context.Context, in *pb.PrivateDebugAPIRequest) (*pb.PrivateDebugAPIReply, error) {
	api.b.SetHead(in.BlockNumber)
	return nil, nil
}

// PublicNetAPIServer offers network related RPC methods
type PublicNetAPIServer struct {
	net            *p2p.Server
	networkVersion uint64
}

// NewPublicNetAPIServer creates a new net APIServer instance.
func NewPublicNetAPIServer(net *p2p.Server, networkVersion uint64) *PublicNetAPIServer {
	return &PublicNetAPIServer{net, networkVersion}
}
func (api *PublicNetAPIServer) RegisterServer(s *grpc.Server) {
	pb.RegisterPublicNetAPIServer(s, api)
}

func (api *PublicNetAPIServer) RegisterProxy(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	pb.RegisterPublicNetAPIHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// Listening returns an indication if the node is listening for network connections.
func (s *PublicNetAPIServer) Listening(ctx context.Context, in *empty.Empty) (*pb.PublicNetAPIReply, error) {
	// always listening
	return &pb.PublicNetAPIReply{
		IsListening: true,
	}, nil
}

// PeerCount returns the number of connected peers
func (s *PublicNetAPIServer) PeerCount(ctx context.Context, in *empty.Empty) (*pb.PublicNetAPIReply, error) {
	return &pb.PublicNetAPIReply{
		PeerCount: uint32(s.net.PeerCount()),
	}, nil
}

// Version returns the current ethereum protocol version.
func (s *PublicNetAPIServer) Version(ctx context.Context, in *empty.Empty) (*pb.PublicNetAPIReply, error) {
	return &pb.PublicNetAPIReply{
		Version: fmt.Sprintf("%d", s.networkVersion),
	}, nil
}
