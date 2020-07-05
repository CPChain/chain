package dpor

import (
	"errors"
	"fmt"
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	lru "github.com/hashicorp/golang-lru"
)

const (
	DefaultMaxInitBlockNumber = 180
)

func newDpor(config *configs.DporConfig, number uint64, hash common.Hash, proposers []common.Address,
	validators []common.Address, mode Mode) *Dpor {
	recents, _ := lru.NewARC(10)
	dpor := &Dpor{
		db:          &fakeDb{1},
		recentSnaps: recents,
		dh:          &defaultDporHelper{},
		currentSnap: &DporSnapshot{
			Mode:             mode,
			config:           config,
			Number:           number,
			Hash:             hash,
			RecentProposers:  make(map[uint64][]common.Address),
			RecentValidators: make(map[uint64][]common.Address),
		},
		config: config,
	}
	dpor.currentSnap.setRecentProposers(dpor.currentSnap.Term(), proposers)
	dpor.currentSnap.setRecentValidators(dpor.currentSnap.Term(), validators)
	return dpor
}

func NewDpor(config *configs.DporConfig, number uint64, hash common.Hash, proposers []common.Address,
	validators []common.Address, mode Mode) *Dpor {
	return newDpor(config, number, hash, proposers, validators, mode)
}

func Test_GetCurrentBlock(t *testing.T) {
	// t.Skip("How to struct dpor.chain????")
	db := database.NewMemDatabase()
	gspec := core.DefaultGenesisBlock()
	gspec.GasLimit = 100000000
	gspec.Alloc = core.GenesisAlloc{testBank: {Balance: testBankBalance}}
	config := gspec.Config
	dporConfig := config.Dpor
	dporFakeEngine := NewFaker(dporConfig, db)
	genesis := gspec.MustCommit(db)
	remoteDB := database.NewIpfsDbWithAdapter(database.NewFakeIpfsAdapter())
	// new a chain for dpor
	blocks, _ := core.GenerateChain(config, genesis, dporFakeEngine, db, remoteDB, 10, nil)
	blockchain, _ := core.NewBlockChain(db, nil, gspec.Config, dporFakeEngine, vm.Config{}, remoteDB, nil)
	_, _ = blockchain.InsertChain(blocks)
	dporFakeEngine.SetChain(blockchain)
	if dporFakeEngine.GetCurrentBlock().NumberU64() != 10 {
		t.Errorf("expect %v, but got %v", 10, dporFakeEngine.GetCurrentBlock().NumberU64())
	}
}

func Test_FutureTermOf(t *testing.T) {
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)

	wantResult := (dpor.currentSnap.Number-1)/((dpor.currentSnap.config.TermLen)*(dpor.currentSnap.config.ViewLen)) + TermDistBetweenElectionAndMining + 1
	calcTerm := dpor.FutureTermOf(dpor.currentSnap.Number)
	if !reflect.DeepEqual(calcTerm, wantResult) {
		t.Error("termCalculateExceptresult is wrong...")
	}
}

func Test_VerifyProposerOf(t *testing.T) {
	// 1.proposerList just one mumber:
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	wantResult := true
	testPro, _ := dpor.VerifyProposerOf(common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"), dpor.currentSnap.TermOf(dpor.currentSnap.Number))
	if !reflect.DeepEqual(testPro, wantResult) {
		t.Error("VerifyProposer failed...")
	}
	// 2.several members in proposerList :
	recentAddr := generateABatchAccounts(10)
	dpor1 := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, recentAddr, nil, NormalMode)

	term := dpor1.currentSnap.TermOf(dpor1.currentSnap.Number)
	var i int
	//var testResult bool
	for i = 1; i < (len(recentAddr) + 1); i++ {
		generateAddr := common.HexToAddress("0x" + fmt.Sprintf("%040x", i))
		testResult, _ := dpor1.VerifyProposerOf(generateAddr, term)
		wantResult := true
		if !reflect.DeepEqual(testResult, wantResult) {
			t.Error("VerifyProposer failed...")
		}
	}

}

// ProposersOf returns proposers of given block number
func Test_ProposersOf(t *testing.T) {
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	testval, _ := dpor.ProposersOf(dpor.currentSnap.Number)
	if !reflect.DeepEqual(testval, proposers) {
		t.Error("TestProposer failed...")
	}
}

// ProposerOf returns the proposer of the specified block number by rpt and election calculation
func Test_IsProposerOf(t *testing.T) {
	recentAddr := generateABatchAccounts(44)
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, recentAddr, nil, NormalMode)

	var i int
	var testResult int
	for i = 1; i < (len(recentAddr) + 1); i++ {
		generateAddr := common.HexToAddress("0x" + fmt.Sprintf("%040x", i))
		wantResult, _ := dpor.currentSnap.IsProposerOf(generateAddr, dpor.currentSnap.Number)
		if wantResult {
			testResult++
		}
	}
	equalSigner := reflect.DeepEqual(1, testResult)
	if !equalSigner {
		t.Error("The mining proposer is not be selected... ")
	}

}

func Test_ProposersOfTerm(t *testing.T) {
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	term := dpor.currentSnap.TermOf(dpor.currentSnap.Number)

	wantResult, _ := dpor.ProposersOfTerm(term)
	equalSigner := reflect.DeepEqual(wantResult, proposers)
	if !equalSigner {
		t.Error("TestProposers failed...")
	}
}

func newBlockchain(n int) *core.BlockChain {
	db := database.NewMemDatabase()
	remoteDB := database.NewIpfsDbWithAdapter(database.NewFakeIpfsAdapter())
	gspec := core.DefaultGenesisBlock()
	genesis := gspec.MustCommit(db)
	config := gspec.Config
	dporConfig := config.Dpor
	dporFakeEngine := NewFaker(dporConfig, db)
	blocks, _ := core.GenerateChain(config, genesis, dporFakeEngine, db, remoteDB, n, nil)
	blockchain, _ := core.NewBlockChain(db, nil, gspec.Config, dporFakeEngine, vm.Config{}, remoteDB, nil)
	_, _ = blockchain.InsertChain(blocks)
	return blockchain
}

func Test_InsertChain(t *testing.T) {
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	dpor.chain = newBlockchain(888)
	unknownBlock := types.NewBlock(newHeader(), nil, nil)
	err := dpor.InsertChain(unknownBlock)
	if err != nil {
		t.Fatal(err)
	}
	num, err := dpor.chain.InsertChain(types.Blocks{unknownBlock})
	if err != nil {
		t.Fatal(err)
	}
	if num != 1 {
		t.Fatalf("expect num be %v, but got %v", 1, num)
	}
	t.Log("has or not", dpor.HasBlockInChain(unknownBlock.Hash(), 888))
	t.Log(dpor.chain.GetBlock(unknownBlock.Hash(), 888))
	t.Log(dpor.GetCurrentBlock().Header().Number)

	t.Log(dpor.currentSnap.Number)
	t.Log(dpor.HasBlockInChain(unknownBlock.Hash(), 889))

}

func Test_TermOf(t *testing.T) {
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)

	wantResult := (dpor.currentSnap.Number - 1) / ((dpor.currentSnap.config.TermLen) * (dpor.currentSnap.config.ViewLen))
	calcTerm := dpor.TermOf(dpor.currentSnap.Number)
	if !reflect.DeepEqual(calcTerm, wantResult) {
		t.Error("termCalculateExceptresult is wrong...")
	}

}

func TestDpor_ValidateBlock(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	//hashBytes := dph.sigHash(newHeader).Bytes()

	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	dpor.chain = newBlockchain(888)
	dpor.dh = dph
	unknownBlock := types.NewBlock(&types.Header{GasLimit: configs.DefaultGasLimitPerBlock}, nil, nil)
	err := dpor.ValidateBlock(unknownBlock, true, true)
	errUnknownAncestor := errors.New("unknown ancestor")
	equalSigner := reflect.DeepEqual(err, errUnknownAncestor)
	if !equalSigner {
		t.Error("Call ValidateBlock failed...")
	}

}

func TestDpor_VerifyHeaderWithState(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	d.mode = FakeMode
	d.chain = newBlockchain(888)
	d.dh = dph
	err := d.VerifyHeaderWithState(newHeader(), consensus.Idle)
	if err != nil {
		t.Error("Call verifyHeader with state failed...")
	}
}

func TestDpor_CheckStatus(t *testing.T) {
	dph := &defaultDporHelper{&defaultDporUtil{}}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	d := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, FakeMode)
	d.chain = newBlockchain(888)
	d.dh = dph
	equalSigner := reflect.DeepEqual(d.Status(), d.PbftStatus())
	if !equalSigner {
		t.Error("Check Status failed...")
	}
}
