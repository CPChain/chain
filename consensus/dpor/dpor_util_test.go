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

package dpor

import (
	"crypto/ecdsa"
	"errors"
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/consensus"

	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/hashicorp/golang-lru"
)

func Test_sigHash(t *testing.T) {
	tx1 := types.NewTransaction(0, common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"), big.NewInt(10), 50000, big.NewInt(10), nil)
	tx1, _ = tx1.WithSignature(types.HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))
	newHeader := &types.Header{
		ParentHash:   common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		Coinbase:     common.HexToAddress("0x8888f1F195AFa192CfeE860698584c030f4c9dB1"),
		StateRoot:    common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxsRoot:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptsRoot: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Number:       big.NewInt(1),
		GasLimit:     uint64(3141592),
		GasUsed:      uint64(21000),
		Time:         big.NewInt(1426516743),
		Extra:        common.Hex2Bytes("0000000000000000000000000000000000000000000000000000000000000000"),
		Dpor: types.DporSnap{
			Seal: types.HexToDporSig("0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"),
			Sigs: []types.DporSignature{},
			Proposers: []common.Address{
				common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"),
				common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092"),
				common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465"),
			},
			Validators: []common.Address{},
		},
	}

	type args struct {
		header *types.Header
	}
	tests := []struct {
		name     string
		args     args
		wantHash common.Hash
	}{
		{"sigHash", args{newHeader}, common.HexToHash("0x22c08daa37af74c536f057987c3c9400c5c528528cb784fac2c7d5dfaa337c9c")},
	}

	dporUtil := &defaultDporUtil{}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if gotHash := dporUtil.sigHash(tt.args.header); !reflect.DeepEqual(gotHash, tt.wantHash) {
				t.Errorf("sigHash(%v) = %v, want %v", tt.args.header, gotHash.Hex(), tt.wantHash.Hex())
			}
		})
	}
}

func getAccount(keyStoreFilePath string, passphrase string) (*ecdsa.PrivateKey, *ecdsa.PublicKey, common.Address) {
	// Load account.
	file, err := os.Open(keyStoreFilePath)
	if err != nil {
		log.Fatal(err.Error())
	}

	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	if err != nil {
		log.Fatal(err.Error())
	}

	kst := keystore.NewKeyStore(keyPath, 2, 1)

	// Get account.
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, passphrase)
	if err != nil {
		log.Fatal(err.Error())
	}

	privateKey := key.PrivateKey
	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		log.Fatal("error casting public key to ECDSA")
	}
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)

	return privateKey, publicKeyECDSA, fromAddress
}

func getTestAccount() (common.Address, *ecdsa.PrivateKey) {
	privateKey, _ := crypto.HexToECDSA("fad9c8855b740a0b7ed4c221dbad0f33a83a49cad6b3fe8d5817ac83d38b6a19")
	publicKey := privateKey.Public()
	publicKeyECDSA, _ := publicKey.(*ecdsa.PublicKey)
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	return fromAddress, privateKey
}

func Test_ecrecover(t *testing.T) {

	addr, privKey := getTestAccount()

	tx1 := types.NewTransaction(0, common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"), big.NewInt(10), 50000, big.NewInt(10), nil)
	tx1, _ = tx1.WithSignature(types.HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))
	cache, _ := lru.NewARC(10)

	newHeader := &types.Header{
		ParentHash:   common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		Coinbase:     common.HexToAddress("0x8888f1F195AFa192CfeE860698584c030f4c9dB1"),
		StateRoot:    common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxsRoot:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptsRoot: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Number:       big.NewInt(1),
		GasLimit:     uint64(3141592),
		GasUsed:      uint64(21000),
		Time:         big.NewInt(1426516743),
		Extra:        hexutil.MustDecode("0x0000000000000000000000000000000000000000000000000000000000000000"),
		Dpor: types.DporSnap{
			Proposers: []common.Address{
				addr,
			},
			Sigs:       make([]types.DporSignature, 3),
			Validators: []common.Address{},
		},
	}

	dph := &defaultDporHelper{&defaultDporUtil{}}
	hashBytes := dph.sigHash(newHeader).Bytes()
	hashBytesWithState, _ := HashBytesWithState(hashBytes, consensus.Prepared)
	proposerSig, _ := crypto.Sign(hashBytes, privKey)
	validatorSig, _ := crypto.Sign(hashBytesWithState, privKey)

	copy(newHeader.Dpor.Seal[:], proposerSig[:])
	copy(newHeader.Dpor.Sigs[0][:], validatorSig[:])
	copy(newHeader.Dpor.Sigs[1][:], validatorSig[:])
	copy(newHeader.Dpor.Sigs[2][:], validatorSig[:])

	sigs := &Signatures{
		sigs: make(map[common.Address][]byte),
	}
	sigs.SetSig(
		addr,
		proposerSig,
	)

	existingCache, _ := lru.NewARC(10)
	fmt.Println("newHeader.Hash():", newHeader.Hash().Hex())
	existingCache.Add(newHeader.Hash(), sigs)

	dporUtil := &defaultDporUtil{}
	// get extra2sig for test
	//privateKey, _, loadedAddr := getAccount("$project_dir/src/bitbucket.org/cpchain/chain/examples/cpchain/data/data1/keystore/", "password")
	//extra2Sig, _ := crypto.Sign(dporUtil.sigHash(newHeader).Bytes(), privateKey)
	//fmt.Println("extra2Sig:", extra2Sig)
	//fmt.Println("extra2Sig hex:", common.Bytes2Hex(extra2Sig))
	//fmt.Println("loadedAddr hex:", loadedAddr.Hex())

	noSignerSigHeader := &types.Header{
		Extra: []byte("0x0000000000000000000000000000000000000000000000000000000000000000"),
		Dpor: types.DporSnap{
			Seal: types.DporSignature{},
			Proposers: []common.Address{
				addr,
			},
			Sigs: make([]types.DporSignature, 3),
		},
	}

	copy(noSignerSigHeader.Dpor.Sigs[0][:], validatorSig[:])
	copy(noSignerSigHeader.Dpor.Sigs[1][:], validatorSig[:])
	copy(noSignerSigHeader.Dpor.Sigs[2][:], validatorSig[:])

	type args struct {
		header   *types.Header
		sigcache *lru.ARCCache
	}
	tests := []struct {
		name    string
		args    args
		want    common.Address
		want1   []common.Address
		wantErr bool
	}{
		{"leaderSigHeader already cached,success", args{newHeader, cache}, addr, []common.Address{addr, addr, addr}, false},
		{"no signers' signatures. fail", args{noSignerSigHeader, cache}, common.Address{}, []common.Address{}, true},
		{"success", args{newHeader, cache}, addr, []common.Address{addr, addr, addr}, false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, got1, err := dporUtil.ecrecover(tt.args.header, tt.args.sigcache)
			if (err != nil) != tt.wantErr {
				t.Errorf("ecrecover(%v, %v) error = %v, wantErr %v", tt.args.header, tt.args.sigcache, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("ecrecover got = %v, want %v", got.Hex(), tt.want.Hex())
			}
			if !reflect.DeepEqual(got1, tt.want1) {
				gotAddrs := []string{}
				for _, addr := range got1 {
					gotAddrs = append(gotAddrs, addr.Hex())
				}
				wantAddrs := []string{}
				for _, addr := range tt.want1 {
					wantAddrs = append(wantAddrs, addr.Hex())
				}
				t.Errorf("ecrecover got1 = %v, want %v", strings.Join(gotAddrs, ","),
					strings.Join(wantAddrs, ","))
			}
		})
	}
}

func Test_acceptSigs(t *testing.T) {
	header := &types.Header{
		Coinbase:     addr1,
		Number:       big.NewInt(1),
		TxsRoot:      types.EmptyRootHash,
		ReceiptsRoot: types.EmptyRootHash,
	}
	sigs := &Signatures{
		sigs: make(map[common.Address][]byte),
	}
	for _, signer := range getValidatorAddress() {
		sigs.SetSig(signer, []byte("ok"))
	}

	emptyCache, _ := lru.NewARC(inMemorySnapshots)
	cache, _ := lru.NewARC(inMemorySnapshots)
	cache.Add(header.Hash(), sigs)

	type args struct {
		header   *types.Header
		sigcache *lru.ARCCache
		signers  []common.Address
		termL    uint
	}
	tests := []struct {
		name    string
		args    args
		want    bool
		wantErr bool
	}{
		{"should be false when signer not in cache", args{header, cache, getValidatorAddress()[1:2], 4}, false, false},
		{"should be false when signer not in cache", args{header, emptyCache, getValidatorAddress(), 4}, false, true},
		{"should be true when signer in cache", args{header, cache, getValidatorAddress(), 4}, true, false},
	}

	dporUtil := &defaultDporUtil{}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := dporUtil.acceptSigs(tt.args.header, tt.args.sigcache, tt.args.signers, tt.args.termL)
			if (err != nil) != tt.wantErr {
				t.Errorf("acceptSigs(%v, %v, %v) error = %v, wantErr %v", tt.args.header, tt.args.sigcache, tt.args.signers, err, tt.wantErr)
				return
			}
			if got != tt.want {
				t.Errorf("acceptSigs(%v, %v, %v) = %v, want %v", tt.args.header, tt.args.sigcache, tt.args.signers, got, tt.want)
			}
		})
	}
}

type fakeDBForSignedBlocksRecord struct {
	m map[string][]byte
}

func newFakeDBForSignedBlocksRecord() *fakeDBForSignedBlocksRecord {
	return &fakeDBForSignedBlocksRecord{
		m: make(map[string][]byte),
	}
}

func (f *fakeDBForSignedBlocksRecord) Put(key []byte, value []byte) error {
	fmt.Println("excuting put, key", key, "value", value)
	f.m[string(key)] = value
	return nil
}

func (f *fakeDBForSignedBlocksRecord) Delete(key []byte) error {
	panic("not implemented")
}

func (f *fakeDBForSignedBlocksRecord) Get(key []byte) ([]byte, error) {
	fmt.Println("excuting get, key", key)
	value, ok := f.m[string(key)]
	if ok {
		return value, nil
	}
	return nil, errors.New("no value")
}

func (f *fakeDBForSignedBlocksRecord) Has(key []byte) (bool, error) {
	panic("not implemented")
}

func (f *fakeDBForSignedBlocksRecord) Close() {
	panic("not implemented")
}

func (f *fakeDBForSignedBlocksRecord) NewBatch() database.Batch {
	panic("not implemented")
}

func Test_newSignedBlocksRecord(t *testing.T) {
	db := newFakeDBForSignedBlocksRecord()
	fsbr := newSignedBlocksRecord(db)

	number, hash := generateNH()
	fmt.Println(number, hash)

	fsbr.MarkAsSigned(number, hash)
	if h, ok := fsbr.IfAlreadySigned(number); h != hash || !ok {
		t.Error("hh", "hash", h, "want", hash, "ok", ok)
	}

	// TODO: add more tests here

}

// generate random number and hash
func generateNH() (number uint64, hash common.Hash) {
	number = uint64(time.Now().UnixNano())
	hash = common.BytesToHash(numberToBytes(number))
	return
}
