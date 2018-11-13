package private

import (
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"math/big"
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common/hexutil"
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
		TxPayloadUri: []byte{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
		Participants: getTestParticipants(),
	}
	data, _ := rlp.EncodeToBytes(r)
	return data
}

func preparePrvTxInvalidIpfsData(remoteDB database.RemoteDatabase) []byte {
	hash, _ := remoteDB.Put([]byte{0, 0, 0, 0, 0, 0, 0, 0, 0})
	r := PayloadReplacement{
		TxPayloadUri: hash,
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
	privKey, _ := x509.ParsePKCS1PrivateKey(privKeyBytes)
	return rsa.DecryptPKCS1v15(rand.Reader, privKey, data)
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

func (fakeWallet) EncryptWithRsa(account accounts.Account, plainText []byte) ([]byte, error) {
	panic("implement me")
}

func (fakeWallet) DecryptWithRsa(account accounts.Account, cipherText []byte) ([]byte, error) {
	panic("implement me")
}

func (fakeWallet) RsaPublicKey(account accounts.Account) (*rsakey.RsaPublicKey, error) {
	panic("implement me")
}

func getDecryptor() accounts.AccountRsaDecryptor {
	return &fakeAccountBasedDecryptor{
		privateKey: "0x308204a30201000282010100d065e5942da25a81fc431f46788281a19d2b961ca14cddc09376c7d63d949ae581735cbee1ff96d60b6410a4501d2c9df01ec6152e39600a80f0af1446c5f4ec275a292c5d9d1ef70a07c04c4f0dd1c8e586059002c16e9c4189c47c848adbd06f256a05da7557f3a4d781e7f185a47045eb4926c6db5c45f639091c7c3e1b29c9869f293b97963cdb83f586bf7e35d2ae1745c79baaa9912f2acd46b1fe35112c50eff32d356e6c2edc27dfa5564ad2ce04e8f39de86ddf5eb76e5958b23da580c242653463eec95ca186f916d5709ccae8ede25c1ad4b19cd62b1e1cfe7e6ea53f8fcd3c7812d2ceb89b5cd3e0d7d4926c9627ddd531fc59010b95a30de8a70203010001028201003b4901aac9e0aa06d890efd0c86fb81915f1545f08b42951a3a1e2efdbcceed3e3a3c1fabba84e6cce08c5833917539e0ab5767c880de2789a7dde10d2a1762fc87229cc69454d8dd1d8aaa80ac54faceb3ed94e42ba6c911f43e615d64efa81ad5ce3708ed95b1001111defb211e6d9d9ca39a142691d32f9fcf7ce96b9c457f7725ba60f8b83db5f8c9cafa419cb5e887518623733f41a7406afc2e193763f4ca714bec73df3514c82d4890b5b53650f5d2f72e0ad15180ee7809a2bc8ae18fdb7b9a525bdcb3a66ba9607c00c48791c71b6c51d058717af98d3e8ed72adcbcf0a023ab55ae5fe1845fb67195e9a558886854fc27f6b70a5382045f5ae074102818100df46f0c09eb444a5a2dfda893327682d4294543457a79f2d23cebd847def1b0ab8dac3662c459af1a1adc525254957c6580de7852bfe297b805b1e875cb0509c056ac05b9bab2c65b8204f8ffbeb190884113e3571014bceb73206efbd454779a51c0cab907ef24df5a0d176f238d247dc4aa41f7124ea11c2e6d8008de2ba3902818100eef0b69627e0e907eee0e7238b70ca206595b74f7ece36a05955f7ca50500628e74367bbb068918686f9185d05749b9ac916b683b2e3fb4554ba3d03691a1f1ac90c99c0aa881560600e5c3b7d64b48bce4d03ab8c51e28f6e48dd5c3778400a4cad76a76ac1a9b47da4c8586316a47143e3e944c9d9c6d82d844b39d3cf39df02818100a48062ceb7deff18be1889ad3e0811a40f02b3cb60ad7a044af67e0108bbcac3aa905b188313c165b7860cd322569819e534515877a229b3f94ca9007814db3f286a8f50af2f7d657034360a5243d34cc7e8e0598569bc0d90418684c9812a790061db1fe834ef96ea9ad2d8fcfb4a4a718e78bf45a039e85e1db0153074545902818023bca8f26860813a088666cbb02d5c6de003b6791354306367392e6879fe9e0d3c199ec839a84a2bbec03ede9ad447f9ac9dd30a7b95119ddb0047e3dcb26578921d6a59a0a7ddda9e434794363afbadf55b1b736af74c557b7f366c76776bcc9e8f4b31db0bc02018b2aeac5995a75eb172c30ee0c9cbadc59105d74e50ae2d0281801d051eae3e078597601839a55eedbca499c8e539a9da45a5c7de45b57c3fdeb0c8a2eb8bf34cf7511640fbfe9c4c3bdc824d6afea738890af633fe2a4d0223373010a3bc992094248e03355dfef0e04aa8b122e45e2b5fba27c4636bbe71d09d401625d62e70999d0cf0e509b8f09da683e5ab8350eff925f4e482aedce2c8f8",
		publicKey:  "0x3082010a0282010100d065e5942da25a81fc431f46788281a19d2b961ca14cddc09376c7d63d949ae581735cbee1ff96d60b6410a4501d2c9df01ec6152e39600a80f0af1446c5f4ec275a292c5d9d1ef70a07c04c4f0dd1c8e586059002c16e9c4189c47c848adbd06f256a05da7557f3a4d781e7f185a47045eb4926c6db5c45f639091c7c3e1b29c9869f293b97963cdb83f586bf7e35d2ae1745c79baaa9912f2acd46b1fe35112c50eff32d356e6c2edc27dfa5564ad2ce04e8f39de86ddf5eb76e5958b23da580c242653463eec95ca186f916d5709ccae8ede25c1ad4b19cd62b1e1cfe7e6ea53f8fcd3c7812d2ceb89b5cd3e0d7d4926c9627ddd531fc59010b95a30de8a70203010001",
	}
}

func getTestParticipants() []string {
	return []string{"0x3082010a0282010100d065e5942da25a81fc431f46788281a19d2b961ca14cddc09376c7d63d949ae581735cbee1ff96d60b6410a4501d2c9df01ec6152e39600a80f0af1446c5f4ec275a292c5d9d1ef70a07c04c4f0dd1c8e586059002c16e9c4189c47c848adbd06f256a05da7557f3a4d781e7f185a47045eb4926c6db5c45f639091c7c3e1b29c9869f293b97963cdb83f586bf7e35d2ae1745c79baaa9912f2acd46b1fe35112c50eff32d356e6c2edc27dfa5564ad2ce04e8f39de86ddf5eb76e5958b23da580c242653463eec95ca186f916d5709ccae8ede25c1ad4b19cd62b1e1cfe7e6ea53f8fcd3c7812d2ceb89b5cd3e0d7d4926c9627ddd531fc59010b95a30de8a70203010001",
		"0x3082010a0282010100bc84262a13ceff4b5d3bfb296d594658ce52b2853d88df4393f96644cdb0c5ab8bf72d529422d955e046c225cf67cf311c3c32ca02abf9f0e3cf669dc702ae07fd234a953113c9744ef11bf33c9794e4b57742bcb2139edfdcc1fbc6258414ca4d9872ee59769aa8caecaa5495c891c168963fd6793e19a42e630f9265abaaf8374911c5ac5dc3170f122c5697fabc72fc4604523a4dd629a34510ade89a0eb26e9ad1ba56f0dfcc83294bcbda9b7d97b2e41d6ea2ad84957e4353207ac51753b801206b4ff99df96bcaec37728956b41ebe892eed87543cf41fba2b02401f15d6daa335baecd30f1622f8bf1bfd39ac638eee957dc3c30ed3b6d823708cd0470203010001"}
}

func getOtherParticipants() []string {
	return []string{"0x3082010a0282010100c4e45de3f773a0dedf24cfb0b3e3944e64794d0c98134e0adc7c197ee23d85d768816280000eb048f09761ca38697f4c24e186d07ff4d797e221f697568496fe07cd329442b3783b1ffb1261dd9e33b7f5001275f1bbc25f77f1b693c640e6478fea87ec3a0675b8a45370c178d6e538a6e3ec53ede5fcfe7689c3b003b6cafb6545133ed90725a2a6f886d8bf9294bd683f563a16f9f30fedb528243e777acec8231160e07c08c55c894d55bc4d78d94b8abf33654494753ee210343e4f9f541b58de72713a34606092cb8f3d299c73e03ed3ae972bda36807180e0fde3720d8c2e196a526e2d643005ec08bcc9511202102b64a74ae9f2413aa532542645170203010001",
		"0x3082010a0282010100c41b896062c93243e178e11d146bdecdcacf06b7e561d57a245cebfbf8572864fb6b68556eb453bd66a5c9fef4247692ea3bd9dbb2ee8c1cc252ea3dff518fec37d9b240369bfc0d9708e776f0e3fc907a67f3c950839ffcb5f942114408efc9d931babcaef330106e3db1ec6fdc32ff3a8e2713b5ecc66efb786f857cb3f490093728f4262fbbaf800d55fda578331cfb4e4fde45a7770287498dc41af8efcacf9c7f892ef2933db57c76d7ab94d2d32c2edd18eb98bb5334110188565805d7b6438feb638d4a16d0fd8c24f869da373248e5b0cf8216d69715b5b164dcda884bdec9c7c74f4f1b8fc9f4b5973b8027590c67f410f5f41504bcb7e448edb7bb0203010001"}
}
