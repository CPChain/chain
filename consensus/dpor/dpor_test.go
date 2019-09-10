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
	"reflect"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	addr1 = common.HexToAddress("0xef3dd127de235f15ffb4fc0d71469d1339df6465")
	addr2 = common.HexToAddress("0xc05302acebd0730e3a18a058d7d1cb1204c4a092")
	addr3 = common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")
	addr4 = common.HexToAddress("0x3333333333333333333333333333333333333333")

	validator1 = common.HexToAddress("0x7b2f052a372951d02798853e39ee56c895109992")
	validator2 = common.HexToAddress("0x2f0176cc3a8617b6ddea6a501028fa4c6fc25ca1")
	validator3 = common.HexToAddress("0xe4d51117832e84f1d082e9fc12439b771a57e7b2")
	validator4 = common.HexToAddress("0x32bd7c33bb5060a85f361caf20c0bda9075c5d51")
)

func getProposerAddress() []common.Address {
	proposers := make([]common.Address, 3)
	proposers[0] = addr1
	proposers[1] = addr2
	proposers[2] = addr3
	return proposers
}

func getValidatorAddress() []common.Address {
	validators := make([]common.Address, 4)
	validators[0] = validator1
	validators[1] = validator2
	validators[2] = validator3
	validators[3] = validator4
	return validators
}

func getCandidates() []common.Address {
	return getProposerAddress()
}

func recents() map[uint64]common.Address {
	signers := make(map[uint64]common.Address)
	signers[0] = addr1
	signers[1] = addr2
	return signers
}

func newHeader() *types.Header {
	return &types.Header{
		ParentHash:   common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		Coinbase:     common.HexToAddress("0x8888f1F195AFa192CfeE860698584c030f4c9dB1"),
		StateRoot:    common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxsRoot:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptsRoot: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Number:       big.NewInt(888),
		GasLimit:     uint64(3141592),
		GasUsed:      uint64(21000),
		Time:         big.NewInt(1426516743),
		Extra:        []byte("0x0000000000000000000000000000000000000000000000000000000000000000095e7baea6a6c7c4c2dfeb977efac326af552d87e94b7b6c5a0e526a4d97f9768ad6097bde25c62ac05302acebd0730e3a18a058d7d1cb1204c4a092ef3dd127de235f15ffb4fc0d71469d1339df64650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"),
	}
}

func TestDpor_SignHash(t *testing.T) {
	privKeyInHex := "fad9c8855b740a0b7ed4c221dbad0f33a83a49cad6b3fe8d5817ac83d38b6a19"
	privateKey, err := crypto.HexToECDSA(privKeyInHex)
	if err != nil {
		t.Fatal(err)
	}
	pubKeyTmp := privateKey.Public()
	publicKey, ok := pubKeyTmp.(*ecdsa.PublicKey)
	if !ok {
		t.Fatal("error casting public key to ECDSA")
	}

	coinbase := crypto.PubkeyToAddress(*publicKey)

	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, getProposerAddress(), getValidatorAddress(), NormalMode)
	dpor.coinbase = coinbase
	addrToSign := common.HexToHash("0xef3dd127de235f15ffb4fc0d71469d1339df6465").Bytes()
	dpor.chain = newBlockchain(4)
	dpor.signFn = func(account accounts.Account, hash []byte) ([]byte, error) {
		return crypto.Sign(hash, privateKey)
	}

	wantResult, _ := dpor.SignHash(addrToSign)

	fmt.Println(wantResult)

	got, _ := dpor.signFn(accounts.Account{Address: dpor.Coinbase()}, addrToSign)
	equalSigner := reflect.DeepEqual(wantResult, got)
	if !equalSigner {
		t.Error("Sign Hash using coinbase failed...")
	}

}

func TestDpor_IsMiner(t *testing.T) {
	privKeyInHex := "fad9c8855b740a0b7ed4c221dbad0f33a83a49cad6b3fe8d5817ac83d38b6a19"
	privateKey, err := crypto.HexToECDSA(privKeyInHex)
	if err != nil {
		t.Fatal(err)
	}
	pubKeyTmp := privateKey.Public()
	publicKey, ok := pubKeyTmp.(*ecdsa.PublicKey)
	if !ok {
		t.Fatal("error casting public key to ECDSA")
	}
	coinbase := crypto.PubkeyToAddress(*publicKey)
	//proposers:=make([]common.Address,1)
	//proposers[0]=coinbase
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, getProposerAddress(), getValidatorAddress(), NormalMode)
	dpor.coinbase = coinbase
	//set coinbase as miner
	dpor.SetAsMiner(true)
	wantResult := true
	got := dpor.isMiner
	equalSigner := reflect.DeepEqual(wantResult, got)
	if !equalSigner {
		t.Error("SetMiner failed...")
	}

}

func TestDpor_Status(t *testing.T) {
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, getProposerAddress(), getValidatorAddress(), FakeMode)
	//test consensus engine:
	dpor.SetAsValidator(true)
	//fmt.Println(dpor.isValidator)
	if !reflect.DeepEqual(int32(1), dpor.isValidator) {
		t.Error("set Validater engine failed...")
	}
	dpor.SetToCampaign(false)
	if !reflect.DeepEqual(int32(0), dpor.isToCampaign) {
		t.Error("set ToCampaign failed...")
	}
	//dpor.mode

	if !reflect.DeepEqual(dpor.Mode(), dpor.mode) {
		t.Error("call mode function didn't match...")
	}

	snap := newSnapshot(&configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}, 1, common.Hash{}, getProposerAddress(), getValidatorAddress(), FakeMode)
	dpor.SetCurrentSnap(snap)
	equalSigner := reflect.DeepEqual(snap, dpor.currentSnap)
	if !equalSigner {
		t.Error("set current snap failed...")
	}
	////dpor.signedBlocks.ifAlreadySigned()
	////test signed Blocks:
	//dpor.chain = newBlockchain(888)
	//var hash common.Hash
	//header := &types.Header{
	//	Coinbase:     common.Address{},
	//	Number:       big.NewInt(int64(66)),
	//	ParentHash:   hash,
	//	TxsRoot:      types.EmptyRootHash,
	//	ReceiptsRoot: types.EmptyRootHash,
	//}
	////dpor.signedBlocks
	//dpor.MarkAsSigned(66,header.Hash())
	//fmt.Println(dpor.IfSigned(5))
	//fmt.Println(dpor.mode,"********",dpor.currentSnap.Mode)
}

func Test_SignedBlocks(t *testing.T) {
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, getProposerAddress(), getValidatorAddress(), FakeMode)

	db := newFakeDBForSignedBlocksRecord()
	fsbr := newSignedBlocksRecord(db)
	dpor.signedBlocks = fsbr

	number, hash := generateNH()
	dpor.MarkAsSigned(number, hash)
	wantResult, signFlag := dpor.IfSigned(number)
	if (!reflect.DeepEqual(wantResult, hash)) && (!reflect.DeepEqual(signFlag, true)) {
		t.Error("mark signatures failed...")
	}
}

// generate random number and hash
func generateNAH() (number uint64, hash common.Hash) {
	number = uint64(time.Now().UnixNano())
	hash = common.BytesToHash(numberToBytes(number))
	return
}
