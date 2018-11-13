// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package ethapi

import (
	"bytes"
	"errors"
	"fmt"
	"math"
	"math/big"
	"time"

	"golang.org/x/net/context"

	"bitbucket.org/cpchain/chain/accounts"
	pb "bitbucket.org/cpchain/chain/api/grpc/v1/common"
	"bitbucket.org/cpchain/chain/api/grpc/v1/personal"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/golang/protobuf/ptypes/empty"
	"github.com/golang/protobuf/ptypes/wrappers"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"google.golang.org/grpc"
)

// AccountManager provides an API to access accounts managed by this node.
// It offers methods to create, (un)lock en list accounts. Some methods accept
// passwords and are therefore considered private by default.
type AccountManager struct {
	am        *accounts.Manager
	nonceLock *AddrLocker
	b         Backend
}

// NewAccountManager create a new AccountManager.
func NewAccountManager(b Backend, nonceLock *AddrLocker) *AccountManager {
	return &AccountManager{
		am:        b.AccountManager(),
		nonceLock: nonceLock,
		b:         b,
	}
}

// IsPublic if public default
func (m *AccountManager) IsPublic() bool {
	return true
}

// Namespace namespace
func (m *AccountManager) Namespace() string {
	return "personal"
}

// RegisterServer register api to grpc
func (m *AccountManager) RegisterServer(s *grpc.Server) {
	personal.RegisterAccountManagerServer(s, m)
}

// RegisterJsonRpc register api to restfull json
func (m *AccountManager) RegisterJsonRpc(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	personal.RegisterAccountManagerHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// ListAccounts will return a list of addresses for accounts this node manages.
func (m *AccountManager) ListAccounts(ctx context.Context, in *empty.Empty) (*pb.Accounts, error) {
	accounts := &pb.Accounts{
		Accounts: make([]*pb.Account, 0, 0),
	}
	// addresses := make([]common.Address, 0) // return [] instead of nil if empty
	for _, wallet := range m.am.Wallets() {
		for _, account := range wallet.Accounts() {
			accounts.Accounts = append(accounts.Accounts, &pb.Account{Address: account.Address.Hex()})
		}
	}
	return accounts, nil
}

// ToPbAccount converts accounts.Account to pb.Account
func ToPbAccount(account *accounts.Account) *pb.Account {
	pbAccount := &pb.Account{
		Url:     account.URL.String(),
		Address: account.Address.Hex(),
	}
	return pbAccount
}

// ListWallets will return a list of wallets this node manages.
func (m *AccountManager) ListWallets(ctx context.Context, in *empty.Empty) (*pb.RawWallets, error) {
	// wallets := make([]rawWallet, 0) // return [] instead of nil if empty
	wallets := &pb.RawWallets{
		RawWallets: make([]*pb.RawWallet, 0, 0),
	}
	for _, wallet := range m.am.Wallets() {
		status, failure := wallet.Status()

		raw := &pb.RawWallet{
			Url:    wallet.URL().String(),
			Status: status,
			Accounts: &pb.Accounts{
				Accounts: make([]*pb.Account, 0, len(wallet.Accounts())),
			},
		}
		for i, account := range wallet.Accounts() {
			raw.Accounts.Accounts[i] = ToPbAccount(&account)
		}
		if failure != nil {
			raw.Failure = failure.Error()
		}
		wallets.RawWallets = append(wallets.RawWallets, raw)
	}
	return wallets, nil
}

// OpenWallet initiates a hardware wallet opening procedure, establishing a USB
// connection and attempting to authenticate via the provided passphrase. Note,
// the method may return an extra challenge requiring a second open (e.g. the
// Trezor PIN matrix challenge).
func (m *AccountManager) OpenWallet(ctx context.Context, in *personal.OpenWalletRequest) (*empty.Empty, error) {
	wallet, err := m.am.Wallet(in.Url)
	if err != nil {
		return &empty.Empty{}, err
	}
	pass := ""
	if in.Passphrase != nil {
		pass = in.Passphrase.Value
	}
	return &empty.Empty{}, wallet.Open(pass)
}

// DeriveAccount requests a HD wallet to derive a new account, optionally pinning
// it for later reuse.
func (m *AccountManager) DeriveAccount(ctx context.Context, in *personal.DeriveAccountRequest) (*pb.Account, error) {
	wallet, err := m.am.Wallet(in.Url)
	if err != nil {
		return &pb.Account{}, err
	}
	derivPath, err := accounts.ParseDerivationPath(in.Path)
	if err != nil {
		return &pb.Account{}, err
	}
	if in.Pin == nil {
		in.Pin = new(wrappers.BoolValue)
	}
	account, err := wallet.Derive(derivPath, in.Pin.Value)
	if err != nil {
		return &pb.Account{}, err
	}
	return ToPbAccount(&account), nil
}

// NewAccount will create a new account and returns the address for the new account.
func (m *AccountManager) NewAccount(ctx context.Context, in *personal.NewAccountRequest) (*pb.Address, error) {
	acc, err := fetchKeystore(m.am).NewAccount(in.Password)
	if err == nil {
		return &pb.Address{Address: acc.Address.Hex()}, nil
	}
	return &pb.Address{}, err
}

// fetchKeystore retrives the encrypted keystore from the account manager.
// func fetchKeystore(am *accounts.Manager) *keystore.KeyStore {
// 	return am.Backends(keystore.KeyStoreType)[0].(*keystore.KeyStore)
// }

// ImportRawKey stores the given hex encoded ECDSA key into the key directory,
// encrypting it with the passphrase.
func (m *AccountManager) ImportRawKey(ctx context.Context, in *personal.ImportRawKeyRequest) (*pb.Address, error) {
	key, err := crypto.HexToECDSA(in.Privkey)
	if err != nil {
		return &pb.Address{}, err
	}
	acc, err := fetchKeystore(m.am).ImportECDSA(key, in.Password)
	return &pb.Address{Address: acc.Address.Hex()}, err
}

// UnlockAccount will unlock the account associated with the given address with
// the given password for duration seconds. If duration is nil it will use a
// default of 300 seconds. It returns an indication if the account was unlocked.
func (m *AccountManager) UnlockAccount(ctx context.Context, in *personal.UnlockAccountRequest) (*pb.IsOk, error) {
	const max = uint64(time.Duration(math.MaxInt64) / time.Second)
	var d time.Duration
	if in.Duration == nil {
		d = 300 * time.Second
	} else if in.Duration.Value > max {
		return &pb.IsOk{IsOk: false}, errors.New("unlock duration too large")
	} else {
		d = time.Duration(in.Duration.Value) * time.Second
	}
	err := fetchKeystore(m.am).TimedUnlock(accounts.Account{Address: common.HexToAddress(in.Address)}, in.Password, d)
	return &pb.IsOk{IsOk: (err == nil)}, err
}

// LockAccount will lock the account associated with the given address when it's unlocked.
func (m *AccountManager) LockAccount(ctx context.Context, addr *pb.Address) (*pb.IsOk, error) {
	err := fetchKeystore(m.am).Lock(common.HexToAddress(addr.Address))
	if err != nil {
		return &pb.IsOk{IsOk: false}, err
	}
	return &pb.IsOk{IsOk: true}, nil
}

type GrpcSendTxArgs personal.SendTxArgs

// setDefaults is a helper function that fills in default values for unspecified tx fields.
func (args *GrpcSendTxArgs) setDefaults(ctx context.Context, b Backend) error {
	if args.Gas == nil {
		args.Gas = &wrappers.UInt64Value{Value: 90000}
	}
	if args.GasPrice == nil {
		price, err := b.SuggestPrice(ctx)
		if err != nil {
			return err
		}
		args.GasPrice = &wrappers.UInt64Value{Value: price.Uint64()}
	}
	if args.Value == nil {
		args.Value = &wrappers.UInt64Value{}
	}
	if args.Nonce == nil {
		nonce, err := b.GetPoolNonce(ctx, common.HexToAddress(args.From))
		if err != nil {
			return err
		}
		// args.Nonce = (*hexutil.Uint64)(&nonce)
		args.Nonce = &wrappers.UInt64Value{Value: nonce}
	}
	if args.Data != nil && args.Input != nil && !bytes.Equal(args.Data, args.Data) {
		return errors.New(`Both "data" and "input" are set and not equal. Please use "input" to pass transaction call data.`)
	}
	if args.To == nil {
		// Contract creation
		var input []byte
		if args.Data != nil {
			input = append(input, args.Data...)
		} else if args.Input != nil {
			input = append(input, args.Input...)
		}
		if len(input) == 0 {
			return errors.New(`contract creation without any data provided`)
		}
	}
	return nil
}

func (args *GrpcSendTxArgs) toTransaction() *types.Transaction {
	var input []byte
	if args.Data != nil {
		// input = *args.Data
		input = append(input, args.Data...)
	} else if args.Input != nil {
		input = append(input, args.Input...)
	}
	var tx *types.Transaction
	if args.To == nil {
		tx = types.NewContractCreation(args.Nonce.Value, new(big.Int).SetUint64(args.Value.Value), args.Gas.Value, new(big.Int).SetUint64(args.GasPrice.Value), input)
	} else {
		tx = types.NewTransaction(args.Nonce.Value, common.HexToAddress(args.To.Value), new(big.Int).SetUint64(args.Value.Value), args.Gas.Value, new(big.Int).SetUint64(args.GasPrice.Value), input)
	}

	tx.SetPrivate(args.IsPrivate)

	return tx
}

// signTransactions sets defaults and signs the given transaction
// NOTE: the caller needs to ensure that the nonceLock is held, if applicable,
// and release it after the transaction has been submitted to the tx pool
func (m *AccountManager) signTransaction(ctx context.Context, args *GrpcSendTxArgs) (*types.Transaction, error) {
	// Look up the wallet containing the requested signer
	account := accounts.Account{Address: common.HexToAddress(args.From)}
	wallet, err := m.am.Find(account)
	if err != nil {
		return nil, err
	}
	// Set some sanity defaults and terminate on failure
	if err := (*GrpcSendTxArgs)(args).setDefaults(ctx, m.b); err != nil {
		return nil, err
	}
	// Assemble the transaction and sign with the wallet
	tx := (*GrpcSendTxArgs)(args).toTransaction()

	chainID := m.b.ChainConfig().ChainID
	return wallet.SignTxWithPassphrase(account, args.Passwd, tx, chainID)
}

// SendTransaction will create a transaction from the given arguments and
// tries to sign it with the key associated with args.To. If the given passwd isn't
// able to decrypt the key it fails.
func (m *AccountManager) SendTransaction(ctx context.Context, args *personal.SendTxArgs) (*pb.Hash, error) {
	if args.Nonce == nil {
		// Hold the addresse's mutex around signing to prevent concurrent assignment of
		// the same nonce to multiple accounts.
		m.nonceLock.LockAddr(common.HexToAddress(args.From))
		defer m.nonceLock.UnlockAddr(common.HexToAddress(args.From))
	}
	signed, err := m.signTransaction(ctx, (*GrpcSendTxArgs)(args))
	if err != nil {
		return &pb.Hash{}, err
	}
	hash, err := submitTransaction(ctx, m.b, signed)
	if err != nil {
		return nil, err
	}
	return &pb.Hash{Hash: hash.Hex()}, nil
}

func toPbTransaction() *pb.Transaction {
	return &pb.Transaction{}
}

// SignTransaction will create a transaction from the given arguments and
// tries to sign it with the key associated with args.To. If the given passwd isn't
// able to decrypt the key it fails. The transaction is returned in RLP-form, not broadcast
// to other nodes
func (m *AccountManager) SignTransaction(ctx context.Context, args *personal.SendTxArgs) (*personal.SignTransactionResult, error) {
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
	signed, err := m.signTransaction(ctx, (*GrpcSendTxArgs)(args))
	if err != nil {
		return nil, err
	}
	data, err := rlp.EncodeToBytes(signed)
	if err != nil {
		return nil, err
	}
	// return &SignTransactionResult{data, signed}, nil
	return &personal.SignTransactionResult{
		Raw: data,
		// Tx:  toPbTransaction(signed),
	}, nil
}

// signHash is a helper function that calculates a hash for the given message that can be
// safely used to calculate a signature from.
//
// The hash is calulcated as
//   keccak256("\x19Ethereum Signed Message:\n"${message length}${message}).
//
// This gives context to the signed message and prevents signing of transactions.
// func signHash(data []byte) []byte {
// 	msg := fmt.Sprintf("\x19Ethereum Signed Message:\n%d%s", len(data), data)
// 	return crypto.Keccak256([]byte(msg))
// }

// Sign calculates an Ethereum ECDSA signature for:
// keccack256("\x19Ethereum Signed Message:\n" + len(message) + message))
//
// Note, the produced signature conforms to the secp256k1 curve R, S and V values,
// where the V value will be 27 or 28 for legacy reasons.
//
// The key used to calculate the signature is decrypted with the given password.
//
// https://github.com/ethereum/go-ethereum/wiki/Management-APIs#personal_sign
func (m *AccountManager) Sign(ctx context.Context, in *personal.SignRequest) (*personal.Signature, error) {
	// Look up the wallet containing the requested signer
	account := accounts.Account{Address: common.HexToAddress(in.Addr)}

	wallet, err := m.b.AccountManager().Find(account)
	if err != nil {
		return nil, err
	}
	// Assemble sign the data with the wallet
	signature, err := wallet.SignHashWithPassphrase(account, in.Passwd, signHash(in.Data))
	if err != nil {
		return nil, err
	}
	signature[64] += 27 // Transform V from 0/1 to 27/28 according to the yellow paper
	return &personal.Signature{Signature: signature}, nil
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
// https://github.com/ethereum/go-ethereum/wiki/Management-APIs#personal_ecRecover
func (m *AccountManager) EcRecover(ctx context.Context, in *personal.EcRecoverRequest) (*pb.Address, error) {
	if len(in.Sig) != 65 {
		return &pb.Address{}, fmt.Errorf("signature must be 65 bytes long")
	}
	if in.Sig[64] != 27 && in.Sig[64] != 28 {
		return &pb.Address{}, fmt.Errorf("invalid Ethereum signature (V is not 27 or 28)")
	}
	in.Sig[64] -= 27 // Transform yellow paper V from 27/28 to 0/1

	rpk, err := crypto.SigToPub(signHash(in.Data), in.Sig)
	if err != nil {
		return &pb.Address{}, err
	}
	return &pb.Address{Address: crypto.PubkeyToAddress(*rpk).Hex()}, nil
}

// SignAndSendTransaction was renamed to SendTransaction. This method is deprecated
// and will be removed in the future. It primary goal is to give clients time to update.
func (m *AccountManager) SignAndSendTransaction(ctx context.Context, args *personal.SendTxArgs) (*pb.Hash, error) {
	return m.SendTransaction(ctx, args)
}
