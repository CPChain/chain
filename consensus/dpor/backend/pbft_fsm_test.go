package backend_test

import (
	"errors"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

func TestDporSm_Fsm(T *testing.T) {

	n := 5

	addr1, key1 := loadDefaultAccount(1)
	fkst := newFkst(addr1, key1)

	db := database.NewMemDatabase()
	remoteDB := database.NewIpfsDbWithAdapter(database.NewFakeIpfsAdapter())

	gspec := core.DefaultGenesisBlock()
	gspec.Alloc = core.GenesisAlloc{
		addr1: {Balance: big.NewInt(1000000000000)},
	}
	genesis := gspec.MustCommit(db)

	config := gspec.Config
	dporConfig := config.Dpor

	dporEngine := dpor.New(dporConfig, db)
	dporEngine.Authorize(fkst.addr, fkst.SignHash)

	dporFakeEngine := dpor.NewFaker(dporConfig, db)

	fsm := backend.NewDporSm(dporEngine, 1)

	chain, _ := core.GenerateChain(config, genesis, dporFakeEngine, db, remoteDB, n, nil)
	blockchain, _ := core.NewBlockChain(db, nil, gspec.Config, dporEngine, vm.Config{}, remoteDB, nil)

	_, _, _ = fsm, chain, blockchain

	// blk1, _ := dporEngine.Seal(blockchain, chain[0], nil)

	// test handle preprepare block
	// input, inputType, msg := blk1, backend.BlockType, backend.PreprepareMsgCode
	// output, act, dtype, msg, err := fsm.Fsm(input, inputType, msg)
	// fmt.Println("output", output, "action", act, "data type", dtype, "msg code", msg, "error", err)

}

type fakeKeystore struct {
	addr common.Address
	key  *keystore.Key
}

func newFkst(addr common.Address, key *keystore.Key) *fakeKeystore {
	return &fakeKeystore{
		addr: addr,
		key:  key,
	}
}

func (fk *fakeKeystore) SignHash(account accounts.Account, hash []byte) ([]byte, error) {
	if account.Address == fk.addr {
		return crypto.Sign(hash, fk.key.PrivateKey)
	}
	return nil, errors.New("wrong account")
}
