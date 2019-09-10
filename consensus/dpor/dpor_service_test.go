package dpor

import (
	"fmt"
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
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
		}}
	dpor.currentSnap.setRecentProposers(dpor.currentSnap.Term(), proposers)
	dpor.currentSnap.setRecentValidators(dpor.currentSnap.Term(), validators)
	return dpor
}

func NewDpor(config *configs.DporConfig, number uint64, hash common.Hash, proposers []common.Address,
	validators []common.Address, mode Mode) *Dpor {
	return newDpor(config, number, hash, proposers, validators, mode)
}

func Test_GetCurrentBlock(t *testing.T) {
	t.Skip("How to struct dpor.chain????")
	db := database.NewMemDatabase()
	gspec := core.DefaultGenesisBlock()
	gspec.GasLimit = 100000000
	gspec.Alloc = core.GenesisAlloc{testBank: {Balance: testBankBalance}}
	config := gspec.Config
	dporConfig := config.Dpor
	dporFakeEngine := NewFaker(dporConfig, db)
	fmt.Println(dporFakeEngine.GetCurrentBlock())
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

func Test_VerifyValidatorOf(t *testing.T) {
	// 1.validaterList just one mumber:
	validaters := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, nil, validaters, NormalMode)
	wantResult := true
	testPro, _ := dpor.VerifyValidatorOf(common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"), dpor.currentSnap.TermOf(dpor.currentSnap.Number))
	if !reflect.DeepEqual(testPro, wantResult) {
		t.Error("VerifyProposer failed...")
	}
	// 2.several members in validaterList :
	recentAddr := generateABatchAccounts(10)
	dpor1 := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, nil, recentAddr, NormalMode)

	term := dpor1.currentSnap.TermOf(dpor.currentSnap.Number)
	var i int
	//var testResult bool
	for i = 1; i < (len(recentAddr) + 1); i++ {
		generateAddr := common.HexToAddress("0x" + fmt.Sprintf("%040x", i))
		testResult, _ := dpor1.VerifyValidatorOf(generateAddr, term)
		wantResult := true
		if !reflect.DeepEqual(testResult, wantResult) {
			t.Error("VerifyProposer failed...")
		}
	}
}

func Test_ValidatorsOf(t *testing.T) {
	validaters := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, nil, validaters, NormalMode)
	testval, _ := dpor.ValidatorsOf(dpor.currentSnap.Number)
	if !reflect.DeepEqual(testval, validaters) {
		t.Error("TestValidater failed...")
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
func Test_ValidatorsOfTerm(t *testing.T) {
	validaters := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	dpor := NewDpor(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, nil, validaters, NormalMode)
	term := dpor.currentSnap.TermOf(dpor.currentSnap.Number)

	wantResult, _ := dpor.ValidatorsOfTerm(term)
	equalSigner := reflect.DeepEqual(wantResult, validaters)
	if !equalSigner {
		t.Error("TestValidaters failed...")
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
	fmt.Println(err)
	num, err := dpor.chain.InsertChain(types.Blocks{unknownBlock})
	fmt.Println(err)
	fmt.Println(num)
	fmt.Println(unknownBlock.Hash())
	fmt.Println("has or not", dpor.HasBlockInChain(unknownBlock.Hash(), 888))
	//unknownBlock.Hash()
	fmt.Println(dpor.chain.GetBlock(unknownBlock.Hash(), 888))
	//dpor.BroadcastBlock(unknownBlock,true)
	if err != nil {
		t.Error("Insertchain has some problems...")
	}
	fmt.Println(dpor.GetCurrentBlock().Header().Number)

	fmt.Println(dpor.currentSnap.Number)
	fmt.Println(dpor.HasBlockInChain(unknownBlock.Hash(), 889))

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
