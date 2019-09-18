package backend_test

import (
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/rlp"
)

// Load account. Used for create ContractCaller
func getAccount(keyStoreFilePath string, passphrase string, t *testing.T) keystore.Key {
	ff, err := filepath.Abs("../../../")
	file, err := os.Open(ff + "/examples/cpchain/data/" + keyStoreFilePath)
	if err != nil {
		t.Fatalf("KeyStoreFilePath error, got %v\n", err)
	}

	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	if err != nil {
		t.Fatalf("KeyStoreFilePath error, got %v\n", err)
	}

	kst := keystore.NewKeyStore(keyPath, 2, 1)

	// Get account.
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, passphrase)
	if err != nil {
		t.Fatalf("Get account failed, got %v", err)
	}

	return *key

}

func TestHandler_SetContractCaller(t *testing.T) {
	t.Skip("skip testing this function")
	var key keystore.Key
	key = getAccount("dd1/keystore/", "password", t)
	fmt.Println("sucessfully print")
	fmt.Println(key)
}

func NewHandler() *backend.Handler {
	db := database.NewMemDatabase()
	coinAddr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 66))
	testHandler := backend.NewHandler(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, coinAddr, db)
	return testHandler
}

func TestHandler_Param(t *testing.T) {
	handler := NewHandler()
	equalSigner1 := reflect.DeepEqual(handler.Length(), nil)
	if equalSigner1 {
		t.Error("Get handler length failed...")
	}
	equalSigner2 := reflect.DeepEqual(handler.Coinbase(), nil)
	if equalSigner2 {
		t.Error("Get handler coinbase failed...")
	}
	equalSigner3 := reflect.DeepEqual(handler.Version(), nil)
	if equalSigner3 {
		t.Error("Get handler version failed...")
	}
	equalSigner4 := reflect.DeepEqual(handler.Available(), nil)
	if equalSigner4 {
		t.Error("Get handler available failed...")
	}
	equalSigner5 := reflect.DeepEqual(handler.GetProtocol(), nil)
	if equalSigner5 {
		t.Error("Get handler protocol failed...")
	}
	equalSigner6 := reflect.DeepEqual(handler.Name(), nil)
	if equalSigner6 {
		t.Error("Get handler name failed...")
	}
}

func TestHandler_SetAvailable(t *testing.T) {
	handler := NewHandler()
	before := handler.Available()
	handler.SetAvailable()
	after := handler.Available()
	equalSigner := reflect.DeepEqual(before, after)
	if equalSigner {
		t.Error("Set Available failed...")
	}
}

func TestHandler_SetCoinbase(t *testing.T) {
	handler := NewHandler()
	addr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 66))
	handler.SetCoinbase(addr)
	after := handler.Coinbase()
	equalSigner := reflect.DeepEqual(addr, after)
	if !equalSigner {
		t.Error("Set coinbase failed...")
	}
}

func TestHandler_HandleMsg(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	proposer := common.HexToAddress("0x" + fmt.Sprintf("%040x", 4))
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	handler := NewHandler()
	handler.SetDialer(dialer)
	unknownBlock := types.NewBlock(&types.Header{GasLimit: configs.DefaultGasLimitPerBlock}, nil, nil)
	size, r, err := rlp.EncodeToReader(unknownBlock)
	if err != nil {
		t.Error("failed to encode composed  block", "err", err)

	}
	var startTime time.Time
	msg := p2p.Msg{Code: backend.PreprepareImpeachBlockMsg, Size: uint32(size), Payload: r, ReceivedAt: startTime}
	_, err = handler.HandleMsg(proposer.Hex(), 65, peer, conn, msg)
	if err != nil {
		t.Error("Call function HandlerMsg failed...")
	}
}

func TestHandler_AddPeer(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	privKeyInHex := "fad9c8855b740a0b7ed4c221dbad0f33a83a49cad6b3fe8d5817ac83d38b6a19"
	privateKey, _ := crypto.HexToECDSA(privKeyInHex)
	signFn := func(account accounts.Account, hash []byte) ([]byte, error) {
		return crypto.Sign(hash, privateKey)
	}
	addr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 66))
	d.Authorize(addr, signFn)
	chain := NewBlockchain(6)
	d.SetChainConfig(chain)
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	handler := NewHandler()
	handler.SetDporService(d)
	handler.SetDialer(dialer)
	_, p, _, _ := handler.AddPeer(11, peer, conn)
	equalSigner := reflect.DeepEqual(p, nil)
	if equalSigner {
		t.Error("Add peer failed...")
	}
}

func NewBlockchain(n int) *core.BlockChain {
	db := database.NewMemDatabase()
	remoteDB := database.NewIpfsDbWithAdapter(database.NewFakeIpfsAdapter())
	gspec := core.DefaultGenesisBlock()
	genesis := gspec.MustCommit(db)
	config := gspec.Config
	dporConfig := config.Dpor
	dporFakeEngine := dpor.NewFaker(dporConfig, db)
	blocks, _ := core.GenerateChain(config, genesis, dporFakeEngine, db, remoteDB, n, nil)
	blockchain, _ := core.NewBlockChain(db, nil, gspec.Config, dporFakeEngine, vm.Config{}, remoteDB, nil)
	_, _ = blockchain.InsertChain(blocks)
	return blockchain
}

func TestHandler_RemovePeer(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	addr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 666))
	dialer.AddRemoteProposer(11, 33, peer, conn, addr)
	handler := NewHandler()
	handler.RemovePeer(addr.Hex())
	_, wantResult := handler.GetDialer().GetProposer(addr.Hex())
	if wantResult {
		t.Error("Remove remotepeer failed")
	}
}
