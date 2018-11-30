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
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
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
		Difficulty:   big.NewInt(131072),
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
		MixHash: common.HexToHash("bd4472abb6659ebe3ee06ee4d7b72a00a9f4d001caca51342001075469aff498"),
		Nonce:   types.EncodeNonce(uint64(0xa13a5a8c8f2bb1c4)),
	}

	type args struct {
		header *types.Header
	}
	tests := []struct {
		name     string
		args     args
		wantHash common.Hash
	}{
		{"sigHash", args{newHeader}, common.HexToHash("0x0ee92e96b718c658a3177e6409f78ff3931268d70a59ef08fc2b2aa5548a0865")},
	}

	dporUtil := &defaultDporUtil{}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if gotHash := dporUtil.sigHash(tt.args.header); !reflect.DeepEqual(gotHash, tt.wantHash) {
				t.Errorf("sigHash(%v) = %v, want %v", tt.args.header, gotHash, tt.wantHash)
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

func Test_ecrecover(t *testing.T) {
	addr := common.HexToAddress("0x8a62173DF795a4eBC4e51A6062277121424b6469")
	//addr := common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")

	tx1 := types.NewTransaction(0, common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"), big.NewInt(10), 50000, big.NewInt(10), nil)
	tx1, _ = tx1.WithSignature(types.HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))
	cache, _ := lru.NewARC(10)

	newHeader := &types.Header{
		ParentHash:   common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		Coinbase:     common.HexToAddress("0x8888f1F195AFa192CfeE860698584c030f4c9dB1"),
		StateRoot:    common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxsRoot:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptsRoot: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Difficulty:   big.NewInt(131072),
		Number:       big.NewInt(1),
		GasLimit:     uint64(3141592),
		GasUsed:      uint64(21000),
		Time:         big.NewInt(1426516743),
		Extra:        hexutil.MustDecode("0x0000000000000000000000000000000000000000000000000000000000000000"),
		Dpor: types.DporSnap{
			Seal: types.HexToDporSig("0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"),
			Proposers: []common.Address{
				common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"),
			},
			Sigs: []types.DporSignature{
				types.HexToDporSig("0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"),
				types.HexToDporSig("0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"),
				types.HexToDporSig("0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"),
			},
			Validators: []common.Address{},
		},
		MixHash: common.HexToHash("bd4472abb6659ebe3ee06ee4d7b72a00a9f4d001caca51342001075469aff498"),
		Nonce:   types.EncodeNonce(uint64(0xa13a5a8c8f2bb1c4)),
	}

	sigs := &Signatures{
		sigs: make(map[common.Address][]byte),
	}
	sigs.SetSig(
		addr,
		hexutil.MustDecode("0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"),
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
				common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"),
			},
			Sigs: []types.DporSignature{
				types.HexToDporSig("0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"),
				types.HexToDporSig("0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"),
				types.HexToDporSig("0xc9efd3956760d72613081c50294ad582d0e36bea45878f3570cc9e8525b997472120d0ef25f88c3b64122b967bd5063633b744bc4e3ae3afc316bb4e5c7edc1d00"),
			},
		},
	}

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
		Difficulty:   big.NewInt(int64(1)),
		TxsRoot:      types.EmptyRootHash,
		ReceiptsRoot: types.EmptyRootHash,
	}
	sigs := &Signatures{
		sigs: make(map[common.Address][]byte),
	}
	for _, signer := range getValidatorAddress() {
		sigs.SetSig(signer, []byte("ok"))
	}

	emptyCache, _ := lru.NewARC(inmemorySnapshots)
	cache, _ := lru.NewARC(inmemorySnapshots)
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

func Test_calcDifficulty(t *testing.T) {
	signers := getProposerAddress()
	config := &configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}
	snapshot := newSnapshot(config, 1, common.Hash{}, signers, []common.Address{})

	type args struct {
		snap   *DporSnapshot
		signer common.Address
	}
	tests := []struct {
		name string
		args args
		want *big.Int
	}{
		{name: "WhenSnapshotSigner1", args: args{snapshot, signers[0]}, want: big.NewInt(1)},
		{name: "WhenSnapshotSigner2", args: args{snapshot, signers[1]}, want: big.NewInt(1)},
	}
	dporUtil := &defaultDporUtil{}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := dporUtil.calcDifficulty(tt.args.snap, tt.args.signer); !reflect.DeepEqual(got, tt.want) {
				t.Errorf("CalcDifficulty(%v, %v) = %v, want %v", tt.args.snap, tt.args.signer, got, tt.want)
			}
		})
	}
}
