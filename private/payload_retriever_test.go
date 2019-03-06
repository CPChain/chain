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

package private

import (
	"math/big"
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/commons/crypto/ecieskey"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/crypto/ecies"
	"github.com/ethereum/go-ethereum/rlp"
)

const txNonceForTest uint64 = 100

// TestRetrieveAndDecryptPayload tests retrieving and decrypting payload.
func TestRetrieveAndDecryptPayload(t *testing.T) {
	// Prepare fake IPFS for testing.
	ipfsAdapter := database.NewFakeIpfsAdapter()
	ipfsDb := database.NewIpfsDbWithAdapter(ipfsAdapter)

	dec := getDecryptor()

	type args struct {
		data                  []byte
		txNonce               uint64
		remoteDb              database.RemoteDatabase
		accountBasedDecryptor accounts.AccountRsaDecryptor
	}
	tests := []struct {
		name              string
		args              args
		wantPayload       []byte
		wantHasPermission bool
		wantErr           bool
	}{
		{
			name: "TestNormalCase",
			args: args{
				data:                  preparePrvTxDataForTesting(ipfsDb),
				txNonce:               txNonceForTest,
				remoteDb:              ipfsDb,
				accountBasedDecryptor: dec,
			},
			wantPayload:       getExpectedPayload(),
			wantHasPermission: true,
			wantErr:           false,
		},
		{
			// Simulate that the replacement written into private tx's payload filed is invalid.
			name: "TestWithInvalidTxPayloadReplacement",
			args: args{
				data:                  []byte{2, 3, 3, 3, 3, 3, 3, 3, 3},
				txNonce:               txNonceForTest,
				remoteDb:              ipfsDb,
				accountBasedDecryptor: dec,
			},
			wantPayload:       []byte{},
			wantHasPermission: false,
			wantErr:           true,
		},
		{
			name: "TestWhenLostDataInIPFS",
			args: args{
				data:                  preparePrvTxPretendedLostDataInIpfs(),
				txNonce:               txNonceForTest,
				remoteDb:              ipfsDb,
				accountBasedDecryptor: dec,
			},
			wantPayload:       []byte{},
			wantHasPermission: false,
			wantErr:           true,
		},
		{
			name: "TestWithInvalidDataInIPFS",
			args: args{
				data:                  preparePrvTxInvalidIpfsData(ipfsDb),
				txNonce:               txNonceForTest,
				remoteDb:              ipfsDb,
				accountBasedDecryptor: dec,
			},
			wantPayload:       []byte{},
			wantHasPermission: false,
			wantErr:           true,
		},
		{
			name: "TestUnauthorizedPrivateTx",
			args: args{
				data:                  prepareUnauthorizedPrvTx(ipfsDb),
				txNonce:               txNonceForTest,
				remoteDb:              ipfsDb,
				accountBasedDecryptor: dec,
			},
			wantPayload:       []byte{},
			wantHasPermission: false,
			wantErr:           false,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			gotPayload, gotHasPermission, err := RetrieveAndDecryptPayload(tt.args.data, tt.args.txNonce, tt.args.remoteDb, tt.args.accountBasedDecryptor)
			if (err != nil) != tt.wantErr {
				t.Errorf("RetrieveAndDecryptPayload() error = %v, wantErr %v", err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(gotPayload, tt.wantPayload) {
				t.Errorf("RetrieveAndDecryptPayload() gotPayload = %v, want %v", gotPayload, tt.wantPayload)
			}
			if gotHasPermission != tt.wantHasPermission {
				t.Errorf("RetrieveAndDecryptPayload() gotHasPermission = %v, want %v", gotHasPermission, tt.wantHasPermission)
			}
		})
	}
}

func Test_decryptPayload(t *testing.T) {
	var (
		cipherPayloadForTest = hexutil.MustDecode("0x216ae6a5c5e0a016d8a95d367b5798cd4bc7fcc51301aadf02e87e1be740bc50ddbfee4b3beecc83594d9f49")
		symmetricKey         = hexutil.MustDecode("0x4f2f80b8ec728f9b583180246127c070e6b75fc0db354d2a080b6ae443ea65f5")
		invalidSymKey        = hexutil.MustDecode("0x000000")
	)

	type args struct {
		cipherdata []byte
		skey       []byte
		txNonce    uint64
	}
	tests := []struct {
		name    string
		args    args
		want    []byte
		wantErr bool
	}{
		{
			name: "TestNormalCase",
			args: args{
				cipherdata: cipherPayloadForTest,
				skey:       symmetricKey,
				txNonce:    txNonceForTest,
			},
			want:    getExpectedPayload(),
			wantErr: false,
		},
		{
			name: "TestWithInvalidSymmetricKey",
			args: args{
				cipherdata: cipherPayloadForTest,
				skey:       invalidSymKey,
				txNonce:    txNonceForTest,
			},
			want:    []byte{},
			wantErr: true,
		},
		{
			name: "TestWithWrongNonce",
			args: args{
				cipherdata: cipherPayloadForTest,
				skey:       symmetricKey,
				txNonce:    txNonceForTest + 1,
			},
			want:    []byte{},
			wantErr: true,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := decryptPayload(tt.args.cipherdata, tt.args.skey, tt.args.txNonce)
			if (err != nil) != tt.wantErr {
				t.Errorf("decryptPayload() error = %v, wantErr %v", err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("decryptPayload() = %v, want %v", got, tt.want)
			}
		})
	}
}

// preparePrvTxDataForTesting prepares the situation on given IPFS database for testing:
// 1. Encrypt and seal payload
// 2. Save it to IPFS
// 3. Return tx payload replacement generated by returned URI of data in IPFS.
func preparePrvTxDataForTesting(remoteDB database.RemoteDatabase) []byte {
	p, _ := SealPrivatePayload(getExpectedPayload(), txNonceForTest, getTestParticipants(), remoteDB)
	data, _ := rlp.EncodeToBytes(p)
	return data
}

// preparePrvTxPretendedLostDataInIpfs pretends the situation where data in IPFS is lost and returns a replacement with the
// URI linking to the lost data.
func preparePrvTxPretendedLostDataInIpfs() []byte {
	r := PayloadReplacement{
		TxPayload:    []byte{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
		Participants: getTestParticipants(),
	}
	data, _ := rlp.EncodeToBytes(r)
	return data
}

func preparePrvTxInvalidIpfsData(remoteDB database.RemoteDatabase) []byte {
	hash, _ := remoteDB.Put([]byte{0, 0, 0, 0, 0, 0, 0, 0, 0})
	r := PayloadReplacement{
		TxPayload:    hash,
		Participants: getTestParticipants(),
	}
	data, _ := rlp.EncodeToBytes(r)
	return data
}

func prepareUnauthorizedPrvTx(remoteDB database.RemoteDatabase) []byte {
	p, _ := SealPrivatePayload(getExpectedPayload(), txNonceForTest, getOtherParticipants(), remoteDB)
	data, _ := rlp.EncodeToBytes(p)
	return data
}

func getExpectedPayload() []byte {
	return []byte("This is an expected payload.")
}

type fakeAccountBasedDecryptor struct {
	privateKey string
	publicKey  string
}

func (self *fakeAccountBasedDecryptor) CanDecrypt(rsaPubkey string) (canDecrypt bool, wallet accounts.Wallet, account *accounts.Account) {
	return self.publicKey == rsaPubkey, fakeWallet{}, &accounts.Account{}
}

func (self *fakeAccountBasedDecryptor) Decrypt(data []byte, wallet accounts.Wallet, account *accounts.Account) ([]byte, error) {
	privKeyBytes, _ := hexutil.Decode(self.privateKey)
	privKey := ecieskey.DecodeEcdsaPrivateKey(privKeyBytes)
	prvEcies := ecies.ImportECDSA(privKey)
	return ecieskey.Decrypt(prvEcies, data)
}

type fakeWallet struct{}

func (fakeWallet) URL() accounts.URL {
	panic("implement me")
}

func (fakeWallet) Status() (string, error) {
	panic("implement me")
}

func (fakeWallet) Open(passphrase string) error {
	panic("implement me")
}

func (fakeWallet) Close() error {
	panic("implement me")
}

func (fakeWallet) Accounts() []accounts.Account {
	panic("implement me")
}

func (fakeWallet) Contains(account accounts.Account) bool {
	panic("implement me")
}

func (fakeWallet) Derive(path accounts.DerivationPath, pin bool) (accounts.Account, error) {
	panic("implement me")
}

func (fakeWallet) SelfDerive(base accounts.DerivationPath, chain cpchain.ChainStateReader) {
	panic("implement me")
}

func (fakeWallet) SignHash(account accounts.Account, hash []byte) ([]byte, error) {
	panic("implement me")
}

func (fakeWallet) SignTx(account accounts.Account, tx *types.Transaction, chainID *big.Int) (*types.Transaction, error) {
	panic("implement me")
}

func (fakeWallet) SignHashWithPassphrase(account accounts.Account, passphrase string, hash []byte) ([]byte, error) {
	panic("implement me")
}

func (fakeWallet) SignTxWithPassphrase(account accounts.Account, passphrase string, tx *types.Transaction, chainID *big.Int) (*types.Transaction, error) {
	panic("implement me")
}

func (fakeWallet) DecryptWithEcies(account accounts.Account, cipherText []byte) ([]byte, error) {
	panic("implement me")
}

func (fakeWallet) PublicKey(account accounts.Account) ([]byte, error) {
	panic("implement me")
}

func getDecryptor() accounts.AccountRsaDecryptor {
	return &fakeAccountBasedDecryptor{
		privateKey: "0xb71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291",
		publicKey:  "0x04ca634cae0d49acb401d8a4c6b6fe8c55b70d115bf400769cc1400f3258cd31387574077f301b421bc84df7266c44e9e6d569fc56be00812904767bf5ccd1fc7f",
	}
}

func getTestParticipants() []string {
	return []string{
		"0x04ca634cae0d49acb401d8a4c6b6fe8c55b70d115bf400769cc1400f3258cd31387574077f301b421bc84df7266c44e9e6d569fc56be00812904767bf5ccd1fc7f",
		"0x04ca634cae0d49acb401d8a4c6b6fe8c55b70d115bf400769cc1400f3258cd31387574077f301b421bc84df7266c44e9e6d569fc56be00812904767bf5ccd1fc7f"}
}

func getOtherParticipants() []string {
	return []string{
		"0x04ed7c2d05e792b6b357a0461adceb0597e5d3988ea95af8eb8a0842cff763b79032103f064b5947bbe3610f45e72e794d9a9a976d6dd5d5181ba08b6038e10772",
		"0x04ed7c2d05e792b6b357a0461adceb0597e5d3988ea95af8eb8a0842cff763b79032103f064b5947bbe3610f45e72e794d9a9a976d6dd5d5181ba08b6038e10772"}
}
