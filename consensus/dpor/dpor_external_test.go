package dpor_test

import (
	"fmt"
	"log"
	"math/big"
	"math/rand"
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/consensus/dpor/campaign"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"bitbucket.org/cpchain/chain/contracts/dpor/admission"
	ca "bitbucket.org/cpchain/chain/contracts/dpor/campaign"
	cr "bitbucket.org/cpchain/chain/contracts/dpor/rpt"
	"bitbucket.org/cpchain/chain/contracts/proxy"
	"bitbucket.org/cpchain/chain/contracts/reward"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

const (
	DefaultMaxInitBlockNumber           = 180
	NormalMode                dpor.Mode = iota
)

var (
	testBankKey, _  = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	testBank        = crypto.PubkeyToAddress(testBankKey.PublicKey)
	testBankBalance = new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))
	rptAddr         common.Address
	rewardAddr      common.Address
	campaignAddr    common.Address
	acAddr          common.Address
)

func generateABatchAccounts(n int) []common.Address {
	var addresses []common.Address
	for i := 1; i < n; i++ {
		addresses = append(addresses, common.HexToAddress("0x"+fmt.Sprintf("%040x", i)))
	}
	return addresses
}

func newBlockchainWithDb(n int, addrs []common.Address) (common.Address, common.Address, *backends.SimulatedBackend) {
	db := database.NewMemDatabase()
	remoteDB := database.NewIpfsDbWithAdapter(database.NewFakeIpfsAdapter())
	gspec := core.DefaultGenesisBlock()
	gspec.GasLimit = 100000000
	gspec.Alloc = core.GenesisAlloc{testBank: {Balance: testBankBalance}}
	genesis := gspec.MustCommit(db)
	config := gspec.Config
	dporConfig := config.Dpor
	dporFakeEngine := dpor.NewFaker(dporConfig, db)
	from := 0
	generator := func(i int, gen *core.BlockGen) {
		number := rand.Intn(10)
		a := int64(number)
		tx := types.NewTransaction(
			gen.TxNonce(testBank),
			addrs[from],
			new(big.Int).Mul(big.NewInt(a), big.NewInt(configs.Cpc)),
			configs.TxGas,
			nil,
			nil,
		)
		tx, _ = types.SignTx(tx, types.HomesteadSigner{}, testBankKey)
		gen.AddTx(tx)

		from = (from + 1) % len(addrs)

	}

	blocks, _ := core.GenerateChain(config, genesis, dporFakeEngine, db, remoteDB, n, generator)
	blockchain, _ := core.NewBlockChain(db, nil, gspec.Config, dporFakeEngine, vm.Config{}, remoteDB, nil)
	_, _ = blockchain.InsertChain(blocks)

	backend := backends.NewDporSimulatedBackendWithExistsBlockchain(db, blockchain, config)

	var err error
	deployTransactor := bind.NewKeyedTransactor(testBankKey)

	rptAddr, _, _, err := cr.DeployRpt(deployTransactor, backend)
	_, _, _, err = proxy.DeployProxyContractRegister(deployTransactor, backend)
	rewardAddr, _, _, err = reward.DeployReward(deployTransactor, backend)
	acAddr, _, _, err = admission.DeployAdmission(deployTransactor, backend, big.NewInt(5), big.NewInt(5), big.NewInt(10), big.NewInt(10))
	campaignAddr, _, _, err = ca.DeployCampaign(deployTransactor, backend, acAddr, rewardAddr)
	if err != nil {
		log.Fatal(err.Error())
	}
	backend.Commit()

	return rptAddr, campaignAddr, backend
}

func TestUpdateRpts(t *testing.T) {
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}

	recentC := generateABatchAccounts(3)
	snapshot := dpor.NewSnapshot(&configs.DporConfig{Period: 3, TermLen: 4, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	snapshot.Candidates = recentC
	accounts := generateABatchAccounts(8)
	contractAddr, _, backend := newBlockchainWithDb(60, accounts)
	rptInstance, _ := rpt.NewRptService(contractAddr, backend)
	rpts, err := snapshot.UpdateRpts(rptInstance)
	if err != nil {
		t.Error("UpdateRpts has some problems...", err)
	}
	// rptservice is not nil...
	t.Log("candidates'rpt format... ", rpts.FormatString())
	// rptservive is nil
	rpts1, err := snapshot.UpdateRpts(nil)
	if err != nil {
		t.Error("UpdateRpts has some problems...", err)
	}
	t.Log("after update rpts of candidate...", rpts1.FormatString())

}

func TestUpdateCandidates(t *testing.T) {
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	recentC := generateABatchAccounts(1000)
	snapshot := dpor.NewSnapshot(&configs.DporConfig{Period: 3, TermLen: 4, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	snapshot.Candidates = recentC

	accounts := generateABatchAccounts(8)
	_, contractAddr, backend := newBlockchainWithDb(60, accounts)
	campaignInstance, _ := campaign.NewCampaignService(contractAddr, backend)

	//NewCampaignService is not nil...
	_ = snapshot.UpdateCandidates(campaignInstance, 33)

	//len(cds)) >= s.Config.TermLen
	t.Log(snapshot.Candidates)

	_ = snapshot.UpdateCandidates(campaignInstance, 33)
	t.Log(snapshot.Candidates)

}

func TestDporSnapshot_updateProposersTermlen4(t *testing.T) {
	//set TermLen 4 && Isstart election...
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	snapshot := dpor.NewSnapshot(&configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)

	accounts := generateABatchAccounts(8)
	contractAddr, _, backend := newBlockchainWithDb(60, accounts)
	rptInstance, _ := rpt.NewRptService(contractAddr, backend)
	rpts := rptInstance.CalcRptInfoList(accounts, 6)

	term := snapshot.FutureTermOf(snapshot.Number)
	beforePros := snapshot.GetRecentProposers(term)
	snapshot.UpdateProposers(rpts, 55, rptInstance)
	afterPros := snapshot.GetRecentProposers(term)

	equalSigner := reflect.DeepEqual(beforePros, afterPros)
	if equalSigner {
		t.Error("Update Proposers failed...")
	}

}

func TestDporSnapshot_updateProposersTermlen12(t *testing.T) {
	//set TermLen 12 && Isstart election...
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	snapshot := dpor.NewSnapshot(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, nil, NormalMode)
	//account num >=8
	accounts := generateABatchAccounts(3)
	contractAddr, _, backend := newBlockchainWithDb(60, accounts)
	rptInstance, _ := rpt.NewRptService(contractAddr, backend)
	rpts := rptInstance.CalcRptInfoList(accounts, 6)

	term := snapshot.FutureTermOf(snapshot.Number)
	beforePros := snapshot.GetRecentProposers(term)
	snapshot.UpdateProposers(rpts, 55, rptInstance)
	afterPros := snapshot.GetRecentProposers(term)
	equalSigner := reflect.DeepEqual(beforePros, afterPros)
	if equalSigner {
		t.Error("Update Proposers failed...")
	}

}

func TestSnapshot_applyHeader(t *testing.T) {
	var hash common.Hash
	header := &types.Header{
		Coinbase:     common.Address{},
		Number:       big.NewInt(int64(5)),
		ParentHash:   hash,
		TxsRoot:      types.EmptyRootHash,
		ReceiptsRoot: types.EmptyRootHash,
	}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	recentA := generateABatchAccounts(5)
	snapshot := dpor.NewSnapshot(&configs.DporConfig{Period: 3, TermLen: 12, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 888, common.Hash{}, proposers, recentA, NormalMode)

	accounts := generateABatchAccounts(20)
	rptAddr, campaignAddr, backend := newBlockchainWithDb(100, accounts)
	rptInstance, _ := rpt.NewRptService(rptAddr, backend)
	campaignInstance, _ := campaign.NewCampaignService(campaignAddr, backend)
	ifUpdateCommittee := true
	snapshot.ApplyHeader(header, ifUpdateCommittee, campaignInstance, rptInstance)
	wantError := false
	if err := snapshot.ApplyHeader(header, ifUpdateCommittee, campaignInstance, rptInstance); (err != nil) != wantError {
		t.Errorf("DporSnapshot.applyHeader(%v) error = %v, wantErr %v", header, err, wantError)
	}

}
