// Copyright 2019 The cpchain authors

package keystore

import (
	"fmt"
	"math/big"
	"math/rand"
	"os"
	"path/filepath"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/assert"
)

var (
	accountString = "01"

	testURL = accounts.URL{Scheme: "aaa", Path: "bbb"}

	accountNoURL   = accounts.Account{Address: common.HexToAddress(accountString)}
	accountWithURL = accounts.Account{Address: common.HexToAddress(accountString), URL: testURL}
)

func TestStatusLocked(t *testing.T) {
	rand.Seed(time.Now().UnixNano())
	dir := filepath.Join(os.TempDir(), fmt.Sprintf("eth-keystore-watch-test-%d-%d", os.Getpid(), rand.Int()))
	ks := NewKeyStore(dir, LightScryptN, LightScryptP)
	kw := &keystoreWallet{
		account:  accounts.Account{Address: common.HexToAddress(accountString)},
		keystore: ks}
	status, err := kw.Status()
	assert.Equal(t, "Locked", status)
	assert.Nil(t, err)
}

func TestStatusUnlocked(t *testing.T) {
	rand.Seed(time.Now().UnixNano())
	dir := filepath.Join(os.TempDir(), fmt.Sprintf("eth-keystore-watch-test-%d-%d", os.Getpid(), rand.Int()))
	ks := NewKeyStore(dir, LightScryptN, LightScryptP)
	ks.unlocked[common.HexToAddress(accountString)] = &unlocked{Key: nil, abort: make(chan struct{})}
	kw := &keystoreWallet{
		account:  accounts.Account{Address: common.HexToAddress(accountString)},
		keystore: ks}
	status, err := kw.Status()
	assert.Equal(t, "Unlocked", status)
	assert.Nil(t, err)
}

func TestOpen(t *testing.T) {
	kw := &keystoreWallet{
		account:  accounts.Account{Address: common.HexToAddress(accountString)},
		keystore: nil}

	err := kw.Open("")
	assert.Nil(t, err)
}

func TestClose(t *testing.T) {
	kw := &keystoreWallet{
		account:  accounts.Account{Address: common.HexToAddress(accountString)},
		keystore: nil}

	err := kw.Close()
	assert.Nil(t, err)
}

func TestContainsTrue(t *testing.T) {
	rand.Seed(time.Now().UnixNano())
	dir := filepath.Join(os.TempDir(), fmt.Sprintf("eth-keystore-watch-test-%d-%d", os.Getpid(), rand.Int()))
	ks := NewKeyStore(dir, LightScryptN, LightScryptP)
	ks.unlocked[common.HexToAddress(accountString)] = &unlocked{Key: nil, abort: make(chan struct{})}
	kw := &keystoreWallet{
		account:  accounts.Account{Address: common.HexToAddress(accountString)},
		keystore: ks}
	account := accounts.Account{Address: common.HexToAddress(accountString)}
	assert.True(t, kw.Contains(account))
}

func TestContainsFalse(t *testing.T) {
	rand.Seed(time.Now().UnixNano())
	dir := filepath.Join(os.TempDir(), fmt.Sprintf("eth-keystore-watch-test-%d-%d", os.Getpid(), rand.Int()))
	ks := NewKeyStore(dir, LightScryptN, LightScryptP)
	ks.unlocked[common.HexToAddress(accountString)] = &unlocked{Key: nil, abort: make(chan struct{})}
	kw := &keystoreWallet{
		account:  accounts.Account{Address: common.HexToAddress(accountString)},
		keystore: ks}

	assert.False(t, kw.Contains(accountWithURL))
}

func TestDerive(t *testing.T) {
	kw := &keystoreWallet{
		account:  accounts.Account{Address: common.HexToAddress(accountString)},
		keystore: nil}

	account, err := kw.Derive(accounts.DerivationPath{0x80000000 + 44, 0x80000000 + 60, 0x80000000 + 0, 0, 0x80000000 + 0}, false)
	assert.Equal(t, accounts.Account{}, account)
	assert.Equal(t, accounts.ErrNotSupported, err)
}

func TestSignHash(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, err := ks.NewAccount(pass)

	ks.Unlock(a1, "")

	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	bs, err := kw.SignHash(a1, testSigData)
	assert.Nil(t, err)
	assert.NotNil(t, bs)
}

func TestSignHashInvalidAccount1(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, err := ks.NewAccount(pass)

	ks.Unlock(a1, "")

	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}

	a1.URL = accounts.URL{Scheme: "sss"}

	bs, err := kw.SignHash(a1, testSigData)
	assert.Nil(t, bs)
	assert.NotNil(t, err)
}

func TestSignHashInvalidAccount(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, err := ks.NewAccount(pass)

	ks.Unlock(a1, "")

	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	bs, err := kw.SignHash(accountNoURL, testSigData)
	assert.Nil(t, bs)
	assert.NotNil(t, err)
}

func TestSignTx(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, err := ks.NewAccount(pass)
	ks.Unlock(a1, "")
	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	transaction := types.NewTransaction(1, common.Address{}, big.NewInt(100), 200, big.NewInt(200), nil)
	bs, err := kw.SignTx(a1, transaction, nil)
	assert.Nil(t, err)
	assert.NotNil(t, bs)
}

func TestSignTxInvalidAccount1(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, err := ks.NewAccount(pass)
	ks.Unlock(a1, "")
	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	transaction := types.NewTransaction(1, common.Address{}, big.NewInt(100), 200, big.NewInt(200), nil)
	a1.URL = accounts.URL{Scheme: "sss"}
	bs, err := kw.SignTx(a1, transaction, nil)
	assert.Nil(t, bs)
	assert.NotNil(t, err)
}
func TestSignTxInvalidAccount(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, err := ks.NewAccount(pass)
	ks.Unlock(a1, "")
	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	transaction := types.NewTransaction(1, common.Address{}, big.NewInt(100), 200, big.NewInt(200), nil)
	bs, err := kw.SignTx(accountNoURL, transaction, nil)
	assert.Nil(t, bs)
	assert.NotNil(t, err)
}

func TestSignHashWithPassphrase(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, err := ks.NewAccount(pass)
	ks.Unlock(a1, "")
	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	bs, err := kw.SignHashWithPassphrase(a1, "", testSigData)
	assert.Nil(t, err)
	assert.NotNil(t, bs)
}

func TestSignHashWithPassphraseInvalidAccount1(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, err := ks.NewAccount(pass)
	ks.Unlock(a1, "")
	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	a1.URL = accounts.URL{Scheme: "sss"}
	bs, err := kw.SignHashWithPassphrase(a1, "", testSigData)
	assert.Nil(t, bs)
	assert.NotNil(t, err)
}

func TestSignHashWithPassphraseInvalidAccount(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, err := ks.NewAccount(pass)
	a1.URL = accounts.URL{Scheme: "aaa", Path: "bbb"}
	ks.Unlock(a1, "")
	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	bs, err := kw.SignHashWithPassphrase(accountNoURL, "", testSigData)
	assert.Nil(t, bs)
	assert.NotNil(t, err)
}

func TestSignTxWithPassphrase(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	a1, err, kw := funcName(ks)
	transaction := types.NewTransaction(1, common.Address{}, big.NewInt(100), 200, big.NewInt(200), nil)
	bs, err := kw.SignTxWithPassphrase(a1, "", transaction, big.NewInt(1))
	assert.Nil(t, err)
	assert.NotNil(t, bs)
}

func funcName(ks *KeyStore) (accounts.Account, error, *keystoreWallet) {
	pass := ""
	a1, err := ks.NewAccount(pass)
	ks.Unlock(a1, "")
	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	return a1, err, kw
}

func TestSignTxWithPassphraseInvalidAccount(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, err := ks.NewAccount(pass)
	ks.Unlock(a1, "")
	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	transaction := types.NewTransaction(1, common.Address{}, big.NewInt(100), 200, big.NewInt(200), nil)
	bs, err := kw.SignTxWithPassphrase(accountNoURL, "", transaction, big.NewInt(1))
	assert.Nil(t, bs)
	assert.NotNil(t, err)
}

func TestSignTxWithPassphraseInvalidAccount1(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, err := ks.NewAccount(pass)
	ks.Unlock(a1, "")
	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	transaction := types.NewTransaction(1, common.Address{}, big.NewInt(100), 200, big.NewInt(200), nil)
	a1.URL = accounts.URL{Scheme: "sss"}
	bs, err := kw.SignTxWithPassphrase(a1, "", transaction, big.NewInt(1))
	assert.Nil(t, bs)
	assert.NotNil(t, err)
}

func TestRsaPublicKey(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, _ := ks.NewAccount(pass)
	ks.Unlock(a1, "")
	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	bs, err := kw.PublicKey(a1)
	assert.Nil(t, err)
	assert.NotNil(t, bs)
}

func TestAccounts(t *testing.T) {
	dir1, ks := tmpKeyStore(t, true)
	defer os.RemoveAll(dir1)
	pass := ""
	a1, _ := ks.NewAccount(pass)
	ks.Unlock(a1, "")
	kw := &keystoreWallet{
		account:  a1,
		keystore: ks}
	accountArray := kw.Accounts()
	assert.Equal(t, 1, len(accountArray))
	assert.Equal(t, a1, accountArray[0])
}
