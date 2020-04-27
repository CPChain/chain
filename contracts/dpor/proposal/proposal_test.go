package proposal_test

import (
	"context"
	"crypto/ecdsa"
	"log"
	"math/big"
	"math/rand"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/contracts/dpor/congress"
	"bitbucket.org/cpchain/chain/contracts/dpor/proposal"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	ownerKey, _     = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	ownerAddr       = crypto.PubkeyToAddress(ownerKey.PublicKey)
	ownerInitAmount = new(big.Int).Mul(big.NewInt(1000), big.NewInt(configs.Cpc))

	bankKey, _     = crypto.HexToECDSA("8a1f9a8f95be41cd7ccb6168179afb4504aefe388d1e14474d32c45c72ce7b7a")
	bankAddr       = crypto.PubkeyToAddress(bankKey.PublicKey)
	bankInitAmount = new(big.Int).Mul(big.NewInt(100000000), big.NewInt(configs.Cpc))

	periodBase      = big.NewInt(1)                                              // second
	amountThreshold = new(big.Int).Mul(big.NewInt(100), big.NewInt(configs.Cpc)) // cpc

	uuid = "68a5281f-f466-45aa-ac72-88e5449cfa3b"
)

func deployCongressContract(prvKey *ecdsa.PrivateKey, backend *backends.SimulatedBackend) (common.Address, *congress.Congress) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	addr, _, instance, err := congress.DeployCongress(deployTransactor, backend)
	if err != nil {
		log.Fatal("deploy congress contract is error :", "error is", err)
	}
	return addr, instance
}

func deployProposalContract(prvKey *ecdsa.PrivateKey, congressContractAddr common.Address, backend *backends.SimulatedBackend) (common.Address, *proposal.Proposal) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	addr, _, instance, err := proposal.DeployProposal(deployTransactor, backend, congressContractAddr)
	if err != nil {
		log.Fatal("deploy proposal contract is error :", "error is", err)
	}
	return addr, instance
}

func initBackend() *backends.SimulatedBackend {
	backend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr: {Balance: ownerInitAmount},
		bankAddr:  {Balance: bankInitAmount},
	})
	backend.Commit()
	return backend
}

func initContracts(backend *backends.SimulatedBackend) (*congress.Congress, *proposal.Proposal) {
	// deploy congress constract
	congressAddr, congressInstance := deployCongressContract(ownerKey, backend)
	backend.Commit()

	// deploy proposal constract
	_, proposalInstance := deployProposalContract(ownerKey, congressAddr, backend)
	backend.Commit()

	return congressInstance, proposalInstance
}

func initContractsWithAddress(backend *backends.SimulatedBackend) (*congress.Congress, *proposal.Proposal, common.Address, common.Address) {
	// deploy congress constract
	congressAddr, congressInstance := deployCongressContract(ownerKey, backend)
	backend.Commit()

	// deploy proposal constract
	proposalAddr, proposalInstance := deployProposalContract(ownerKey, congressAddr, backend)
	backend.Commit()

	return congressInstance, proposalInstance, congressAddr, proposalAddr
}

func TestDeployContracts(t *testing.T) {
	// deploy contract
	backend := initBackend()

	// deploy congress constract
	_, proposalInstance := initContracts(backend)

	if _, err := proposalInstance.GetCongressNum(nil); err != nil {
		t.Fatal("congress's num should be zero", err)
	}

	// deploy proposal constract with a wrong congress address
	_, proposalInstance = deployProposalContract(ownerKey, ownerAddr, backend)
	backend.Commit()

	if _, err := proposalInstance.GetCongressNum(nil); err == nil {
		t.Fatal("congress's address is wrong, there should be a unmarshalling error")
	}
}

func TestSubmitProposal(t *testing.T) {
	// init
	backend := initBackend()
	_, proposalInstance := initContracts(backend)

	ch := make(chan *proposal.ProposalSubmitProposal)
	done := make(chan struct{})
	if _, err := proposalInstance.WatchSubmitProposal(nil, ch); err != nil {
		t.Fatal(err)
	}
	go func() {
		select {
		case e := <-ch:
			if e.Who.Hex() != bankAddr.Hex() {
				t.Error("address of who submited proposal should be equal to bank")
			}
			done <- struct{}{}
		}
	}()

	// normal
	opts := bind.NewKeyedTransactor(bankKey)
	opts.Value = new(big.Int).Mul(big.NewInt(100), big.NewInt(configs.Cpc))

	period := big.NewInt(1)
	id := uuid
	if _, err := proposalInstance.Submit(opts, id, period); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	checkProposalCnt(t, proposalInstance, 1)
	checkID(t, proposalInstance, 0, id)

	checkStatus(t, proposalInstance, id, 0)

	backend.AdjustTime(1000 * time.Second) // time unit is different, adjust time to 1000s, block time add 1 second
	backend.Commit()

	// check timeout
	opts.Value = big.NewInt(0)
	if _, err := proposalInstance.CheckTimeout(opts, id); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	// this proposal should be timeout
	checkStatus(t, proposalInstance, id, 3)

	<-done
}

func TestSubmitWithWrongParams(t *testing.T) {
	// init
	backend := initBackend()
	_, proposalInstance := initContracts(backend)

	// less deposit
	opts := bind.NewKeyedTransactor(bankKey)
	opts.Value = new(big.Int).Mul(big.NewInt(99), big.NewInt(configs.Cpc))

	period := big.NewInt(1)
	id := uuid
	if _, err := proposalInstance.Submit(opts, id, period); err == nil {
		t.Error("This transaction should fail, cause sent value is less than the threshold")
	}
	backend.Commit()

	checkProposalCnt(t, proposalInstance, 0)

	// empty id
	id = ""
	opts.Value = new(big.Int).Mul(big.NewInt(100), big.NewInt(configs.Cpc))
	if _, err := proposalInstance.Submit(opts, id, period); err == nil {
		t.Error("This transaction should fail, cause id is empty")
	}
	backend.Commit()

	checkProposalCnt(t, proposalInstance, 0)

	// period greater than maxPeriod
	id = uuid
	period = big.NewInt(31 * 24 * 60 * 60)
	if _, err := proposalInstance.Submit(opts, id, period); err == nil {
		t.Error("This transaction should fail, cause period is greater than the MaxPeriod")
	}
	backend.Commit()

	checkProposalCnt(t, proposalInstance, 0)

	// submit a successful proposal
	period = big.NewInt(1)
	if _, err := proposalInstance.Submit(opts, id, period); err != nil {
		t.Error(err)
	}
	backend.Commit()

	// submit twice
	if _, err := proposalInstance.Submit(opts, id, period); err == nil {
		t.Error("This transaction should fail, cause id already exists!")
	}
	backend.Commit()
}

func TestApproval(t *testing.T) {
	// init
	backend := initBackend()
	_, proposalInstance := initContracts(backend)

	// submit a proposal
	opts := bind.NewKeyedTransactor(bankKey)
	opts.Value = new(big.Int).Mul(big.NewInt(100), big.NewInt(configs.Cpc))

	period := big.NewInt(1)
	id := uuid
	if _, err := proposalInstance.Submit(opts, id, period); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	// approval this proposal
	opts.Value = big.NewInt(0)
	if _, err := proposalInstance.Approval(opts, id); err != nil {
		t.Error(err)
	}
	backend.Commit()

	// check approval cnt
	checkApprovalCnt(t, proposalInstance, id, 1)
	checkStatus(t, proposalInstance, id, 0)

	// approve again
	if _, err := proposalInstance.Approval(opts, id); err == nil {
		t.Error("This transaction should fail, cause the sender already approved")
	}
	backend.Commit()

	checkApprovalCnt(t, proposalInstance, id, 1)

	// approve a not exists proposal
	if _, err := proposalInstance.Approval(opts, "wrong"); err == nil {
		t.Error("This transaction should fail, cause the proposal not exists")
	}

	// another people to approve proposal
	if key, err := crypto.GenerateKey(); err != nil {
		t.Error(err)
	} else {
		// get nonce of bank key
		nonce, err := backend.NonceAt(context.Background(), bankAddr, backend.Blockchain().CurrentBlock().Number())
		if err != nil {
			t.Error(err)
		}
		// prepare key
		if err := transfer(backend, crypto.PubkeyToAddress(key.PublicKey), nonce, 100); err != nil {
			t.Error(err)
		}
		backend.Commit()

		// make proposal be timeout
		backend.AdjustTime(1000 * time.Second)
		backend.Commit()

		opts := bind.NewKeyedTransactor(key)
		opts.Value = big.NewInt(0)
		if _, err := proposalInstance.Approval(opts, id); err == nil {
			t.Error("This transaction should fail because proposal is timeout")
		}
		backend.Commit()

		checkApprovalCnt(t, proposalInstance, id, 1)
		checkStatus(t, proposalInstance, id, 0)

		// check timeout
		opts.Value = big.NewInt(0)
		if _, err := proposalInstance.CheckTimeout(opts, id); err != nil {
			t.Fatal(err)
		}
		backend.Commit()
		checkStatus(t, proposalInstance, id, 3)

		if _, err := proposalInstance.CheckTimeout(opts, id); err == nil {
			t.Fatal("This transaction should fail because the proposal's sttaus already be timeout.")
		}
		backend.Commit()

		// create another a key
		key1, _ := crypto.GenerateKey()
		nonce, _ = backend.NonceAt(context.Background(), bankAddr, backend.Blockchain().CurrentBlock().Number())
		transfer(backend, crypto.PubkeyToAddress(key1.PublicKey), nonce, 100)
		backend.Commit()

		opts = bind.NewKeyedTransactor(key)
		opts.Value = big.NewInt(0)
		if _, err := proposalInstance.Approval(opts, id); err == nil {
			t.Error("This transaction should fail, cause the proposal is timeout")
		}
		backend.Commit()

		checkApprovalCnt(t, proposalInstance, id, 1)
		checkStatus(t, proposalInstance, id, 3)
	}

}

func TestApprovalUtilThreshold(t *testing.T) {
	// init
	backend := initBackend()
	_, instance := initContracts(backend)

	// update approval cnt threshold
	opts := bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)

	threshold := int64(10)

	if _, err := instance.SetApprovalThreshold(opts, big.NewInt(threshold)); err != nil {
		t.Error(err)
	}

	backend.Commit()

	_t, _ := instance.ApprovalThreshold(nil)
	if threshold != _t.Int64() {
		t.Errorf("threshold should be %v, but got %v", threshold, _t.Int64())
	}

	// generate 10 key
	keys := initKeys(t, backend, int(threshold))

	// submit a proposal
	opts = bind.NewKeyedTransactor(bankKey)
	opts.Value = new(big.Int).Mul(big.NewInt(100), big.NewInt(configs.Cpc))

	period := big.NewInt(1)
	id := uuid
	if _, err := instance.Submit(opts, id, period); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	// approval
	for i, key := range keys {
		opts := bind.NewKeyedTransactor(key)
		opts.Value = big.NewInt(0)
		if _, err := instance.Approval(opts, id); err != nil {
			t.Error(i, err)
		}
		backend.Commit()
		if int64(i) < threshold-1 {
			checkStatus(t, instance, id, 0)
		}
	}
	checkApprovalCnt(t, instance, id, threshold)
	checkStatus(t, instance, id, 1)
}

func TestVote(t *testing.T) {
	var (
		keysCnt = 10
		id      = uuid
	)
	// init
	backend := initBackend()
	congressIns, instance := initContracts(backend)
	_ = congressIns

	// generate 10 key
	keys := initKeys(t, backend, int(keysCnt))

	// update approval threshold to keysCnt
	updateApprovalThreshold(t, backend, instance, keysCnt)

	// submit a proposal
	submitProposal(t, backend, instance, id)

	// status of the proposal is "deposited"
	checkStatus(t, instance, id, 0)

	// approval
	approveAll(t, backend, instance, id, keys)

	checkApprovalCnt(t, instance, id, int64(keysCnt))

	// status of the proposal already has been set to "approved"
	checkStatus(t, instance, id, 1)

	// firstly, use the bankKey to vote proposal, this will fail cause bankKey is not in congress
	opts := bind.NewKeyedTransactor(bankKey)
	opts.Value = big.NewInt(0)

	if _, err := instance.Vote(opts, id); err == nil {
		t.Error("This transaction should fail because the key is not in congress")
	}

	checkVoteCnt(t, instance, id, 0)

	// init congress, add all keys to congress
	initCongress(t, backend, congressIns, keys)

	// check the nums in congress
	checkCongressNum(t, congressIns, keysCnt)

	// update the voteThreshold to 100
	updateVoteThreshold(t, backend, instance, 100)

	// vote
	voteAll(t, backend, instance, id, keys)

	// status of the proposal already has been set to "successful"
	checkStatus(t, instance, id, 2)
	checkVoteCnt(t, instance, id, 10)

	// now, even this proposal timeout, the status won't change
	// make proposal be timeout
	backend.AdjustTime(1000 * time.Second)
	backend.Commit()

	// check timeout
	opts.Value = big.NewInt(0)
	if _, err := instance.CheckTimeout(opts, id); err == nil {
		t.Error("This transaction should fail because status has been changed to successful, no need timeout anymore.")
	}
	backend.Commit()
	checkStatus(t, instance, id, 2)

}

func TestVoteTwice(t *testing.T) {
	var (
		keysCnt = 10
		id      = uuid
	)
	// init
	backend := initBackend()
	congressIns, instance := initContracts(backend)
	_ = congressIns

	// generate 10 key
	keys := initKeys(t, backend, int(keysCnt))

	// update approval threshold to keysCnt
	updateApprovalThreshold(t, backend, instance, keysCnt)

	// update vote threshold to 30%
	updateVoteThreshold(t, backend, instance, 30)

	// submit a proposal
	submitProposal(t, backend, instance, id)

	// approval
	approveAll(t, backend, instance, id, keys)

	// status of the proposal already has been set to "approved"
	checkStatus(t, instance, id, 1)

	// init congress, add all keys to congress
	initCongress(t, backend, congressIns, keys)

	checkVoteCnt(t, instance, id, 0)

	// key1 vote
	if err := vote(t, backend, instance, id, keys[0]); err != nil {
		t.Error(err)
	}

	checkVoteCnt(t, instance, id, 1)

	// key1 vote again
	if err := vote(t, backend, instance, id, keys[0]); err == nil {
		t.Error("This transaction should fail because key1 already voted")
	}

	checkVoteCnt(t, instance, id, 1)

	// vote to a not exists proposal
	if err := vote(t, backend, instance, "not exists", keys[1]); err == nil {
		t.Error("This transaction should fail because proposal is not exists")
	}

	// key2 vote proposal
	if err := vote(t, backend, instance, id, keys[1]); err != nil {
		t.Error(err)
	}

	checkVoteCnt(t, instance, id, 2)
	checkStatus(t, instance, id, 1)

	// key3 vote proposal
	if err := vote(t, backend, instance, id, keys[2]); err != nil {
		t.Error(err)
	}

	checkVoteCnt(t, instance, id, 3)
	checkStatus(t, instance, id, 2)

}

func TestVoteFail(t *testing.T) {
	var (
		keysCnt = 10
		id      = uuid
	)
	// init
	backend := initBackend()
	congressIns, instance := initContracts(backend)

	// generate 10 key
	keys := initKeys(t, backend, int(keysCnt))

	// init congress, add all keys to congress
	initCongress(t, backend, congressIns, keys)

	// update approval threshold to keysCnt
	updateApprovalThreshold(t, backend, instance, keysCnt)

	// update vote threshold to 30%
	updateVoteThreshold(t, backend, instance, 30)

	// submit a proposal
	submitProposal(t, backend, instance, id)

	// key1 approve
	if err := approve(t, backend, instance, id, keys[0]); err != nil {
		t.Error(err)
	}

	checkApprovalCnt(t, instance, id, 1)
	checkStatus(t, instance, id, 0)

	// vote should fail
	if err := vote(t, backend, instance, id, keys[1]); err == nil {
		t.Error("This transaction should be fail because approval count is less than threshold.")
	}

	checkVoteCnt(t, instance, id, 0)
	checkStatus(t, instance, id, 0)

	approveAll(t, backend, instance, id, keys[1:])
	checkStatus(t, instance, id, 1)

	// vote should success
	if err := vote(t, backend, instance, id, keys[0]); err != nil {
		t.Error(err)
	}

	checkStatus(t, instance, id, 1)

	// make proposal be timeout
	backend.AdjustTime(1000 * time.Second)
	backend.Commit()

	// vote should fail
	if err := vote(t, backend, instance, id, keys[2]); err == nil {
		t.Error("This transaction should fail because proposal is timeout", err)
	}

	checkStatus(t, instance, id, 1)
}

func TestWithdrawWithNotExistsID(t *testing.T) {
	var (
		id = uuid
	)
	// init
	backend := initBackend()
	_, instance := initContracts(backend)

	opts := bind.NewKeyedTransactor(bankKey)
	opts.Value = big.NewInt(0)

	if _, err := instance.Withdraw(opts, id); err == nil {
		t.Fatal("This transaction should be fail because id is not exists.")
	}
}

func TestWithdrawWhenStatusIsDeposited(t *testing.T) {
	var (
		id = uuid
	)
	// init
	backend := initBackend()
	_, instance, _, address := initContractsWithAddress(backend)

	balance0, _ := backend.BalanceAt(context.Background(), bankAddr, backend.Blockchain().CurrentBlock().Number())

	// submit a proposal
	submitProposal(t, backend, instance, id)

	// check value of contract address
	value := getBalance(backend, address)
	if value.Cmp(amountThreshold) != 0 {
		t.Fatalf("The balance of contract expect %v, but got %v", amountThreshold, value)
	}

	gasUsedForSubmit := backend.Blockchain().CurrentBlock().GasUsed()

	checkStatus(t, instance, id, 0)

	balance1 := getBalance(backend, bankAddr)
	balanceAfterSubmit := big.NewInt(0).Add(amountThreshold, big.NewInt(int64(gasUsedForSubmit)))
	balanceAfterSubmit = balanceAfterSubmit.Add(balanceAfterSubmit, getBalance(backend, bankAddr))
	if balanceAfterSubmit.Cmp(balance0) != 0 {
		t.Fatalf("Balance of owner is wrong, expect %v but got %v", balance0, balanceAfterSubmit)
	}

	opts := bind.NewKeyedTransactor(bankKey)
	opts.Value = big.NewInt(0)

	if _, err := instance.Withdraw(opts, id); err == nil {
		t.Fatal("This transaction should be fail because the proposal's status is not successful or timeout")
	}

	// make proposal be timeout
	backend.AdjustTime(1000 * time.Second)
	backend.Commit()

	// proposal is timeout now, withdraw will success
	if _, err := instance.Withdraw(opts, id); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	gasUsedForWithdraw := backend.Blockchain().CurrentBlock().GasUsed()

	checkStatus(t, instance, id, 3)

	// check balance
	balanceAfterWithdraw := big.NewInt(0).Add(getBalance(backend, bankAddr), big.NewInt(int64(gasUsedForWithdraw)))
	if balanceAfterWithdraw.Cmp(balance1.Add(balance1, amountThreshold)) != 0 {
		t.Fatalf("Balance of owner is wrong, expect %v but got %v", balance0, balanceAfterSubmit)
	}

	// check value of contract address
	value = getBalance(backend, address)
	if value.Cmp(big.NewInt(0)) != 0 {
		t.Fatalf("The balance of contract expect %v, but got %v", 0, value)
	}

	// withdraw again, will fail
	if _, err := instance.Withdraw(opts, id); err == nil {
		t.Fatal("This transaction should fail because already withdraw.")
	}
}

func TestWithdrawWhenStatusIsAppoved(t *testing.T) {
	var (
		keysCnt = 10
		id      = uuid
	)
	// init
	backend := initBackend()
	congressIns, instance := initContracts(backend)

	// generate 10 key
	keys := initKeys(t, backend, int(keysCnt))

	// init congress, add all keys to congress
	initCongress(t, backend, congressIns, keys)

	// update approval threshold to keysCnt
	updateApprovalThreshold(t, backend, instance, keysCnt)

	// update vote threshold to 30%
	updateVoteThreshold(t, backend, instance, 30)

	// submit a proposal
	submitProposal(t, backend, instance, id)

	// approve all
	approveAll(t, backend, instance, id, keys)

	checkStatus(t, instance, id, 1)

	// withdraw
	opts := bind.NewKeyedTransactor(bankKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.Withdraw(opts, id); err == nil {
		t.Fatal("This transaction should fail because status is approved")
	}
}

func TestWithdrawWhenStatusIsSuccessful(t *testing.T) {
	var (
		keysCnt = 10
		id      = uuid
	)
	// init
	backend := initBackend()
	congressIns, instance := initContracts(backend)

	// generate 10 key
	keys := initKeys(t, backend, int(keysCnt))

	// init congress, add all keys to congress
	initCongress(t, backend, congressIns, append(keys, bankKey))

	// update approval threshold to keysCnt
	updateApprovalThreshold(t, backend, instance, keysCnt)

	// update vote threshold to 30%
	updateVoteThreshold(t, backend, instance, 30)

	// submit a proposal
	submitProposal(t, backend, instance, id)

	// approve all
	approveAll(t, backend, instance, id, keys)

	checkStatus(t, instance, id, 1)

	// get balance of bank-key before voting
	balanceBeforeVoting := getBalance(backend, bankAddr)

	// voteall
	voteAll(t, backend, instance, id, keys)

	checkStatus(t, instance, id, 2)

	// withdraw with another key ranther than owner key
	opts := bind.NewKeyedTransactor(keys[0])
	opts.Value = big.NewInt(0)
	if _, err := instance.Withdraw(opts, id); err == nil {
		t.Fatal("This transaction should fail because the key is not owner")
	}

	// After voting, the locked money has been automatically refunded
	amountThreshold, _ := instance.AmountThreshold(nil)

	balanceAfterVoting := getBalance(backend, bankAddr)

	// calculate balance
	if balanceAfterVoting.Cmp(big.NewInt(0).Add(balanceBeforeVoting, amountThreshold)) != 0 {
		t.Fatalf("the balance is wrong because the locked money has been refunded.")
	}

	// withdraw
	opts = bind.NewKeyedTransactor(bankKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.Withdraw(opts, id); err == nil {
		t.Fatal("This transaction should be fail because the locked money has been automatically refunded.")
	}
}

func TestWithdrawWhenStatusIsTimeout(t *testing.T) {
	var (
		id = uuid
	)
	// init
	backend := initBackend()
	_, instance := initContracts(backend)

	// submit a proposal
	submitProposal(t, backend, instance, id)

	// make proposal be timeout
	backend.AdjustTime(1000 * time.Second)
	backend.Commit()

	// get balance of bank-key before voting
	balanceBeforeTimeout := getBalance(backend, bankAddr)

	opts := bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.CheckTimeout(opts, id); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	// After voting, the locked money has been automatically refunded
	amountThreshold, _ := instance.AmountThreshold(nil)

	balanceAfterTimeout := getBalance(backend, bankAddr)

	// calculate balance
	if balanceAfterTimeout.Cmp(big.NewInt(0).Add(balanceBeforeTimeout, amountThreshold)) != 0 {
		t.Fatalf("the balance is wrong because the locked money has been refunded.")
	}

	checkStatus(t, instance, id, 3)

	opts = bind.NewKeyedTransactor(bankKey)
	opts.Value = big.NewInt(0)

	if _, err := instance.Withdraw(opts, id); err == nil {
		t.Fatal("This transaction should fail because the locked money has been automatically refunded.")
	}
	backend.Commit()
}

func TestWithdrawWhenStatusIsApprovedButTimeout(t *testing.T) {
	var (
		keysCnt = 10
		id      = uuid
	)
	// init
	backend := initBackend()
	congressIns, instance := initContracts(backend)

	// generate 10 key
	keys := initKeys(t, backend, int(keysCnt))

	// init congress, add all keys to congress
	initCongress(t, backend, congressIns, keys)

	// update approval threshold to keysCnt
	updateApprovalThreshold(t, backend, instance, keysCnt)

	// update vote threshold to 30%
	updateVoteThreshold(t, backend, instance, 30)

	// submit a proposal
	submitProposal(t, backend, instance, id)

	// approve all
	approveAll(t, backend, instance, id, keys)

	checkStatus(t, instance, id, 1)

	// make proposal be timeout
	backend.AdjustTime(1000 * time.Second)
	backend.Commit()

	// withdraw
	opts := bind.NewKeyedTransactor(bankKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.Withdraw(opts, id); err != nil {
		t.Fatal(err)
	}
	backend.Commit()
	checkStatus(t, instance, id, 3)
}

func TestWithdrawWhenStatusIsSuccessfulButTimeout(t *testing.T) {
	var (
		keysCnt = 10
		id      = uuid
	)
	// init
	backend := initBackend()
	congressIns, instance := initContracts(backend)

	// generate 10 key
	keys := initKeys(t, backend, int(keysCnt))

	// init congress, add all keys to congress
	initCongress(t, backend, congressIns, keys)

	// update approval threshold to keysCnt
	updateApprovalThreshold(t, backend, instance, keysCnt)

	// update vote threshold to 30%
	updateVoteThreshold(t, backend, instance, 30)

	// submit a proposal
	submitProposal(t, backend, instance, id)

	// approve all
	approveAll(t, backend, instance, id, keys)

	checkStatus(t, instance, id, 1)

	voteAll(t, backend, instance, id, keys)

	// make proposal be timeout
	backend.AdjustTime(1000 * time.Second)
	backend.Commit()

	// withdraw
	opts := bind.NewKeyedTransactor(bankKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.Withdraw(opts, id); err == nil {
		t.Fatal("This transaction should fail because the locked amount had been automatically refunded.")
	}
	backend.Commit()
	checkStatus(t, instance, id, 2)
}

func TestMultiProposals(t *testing.T) {
	var (
		cnt = 10
	)
	backend := initBackend()
	_, instance := initContracts(backend)

	r := rand.New(rand.NewSource(0))

	var list []string

	for i := 0; i < cnt; i++ {
		tmp := randString(r, 36)
		list = append(list, tmp)
		t.Log(tmp)
		submitProposal(t, backend, instance, tmp)
	}

	num, _ := instance.GetProposalsCnt(nil)

	if num.Cmp(big.NewInt(int64(cnt))) != 0 {
		t.Fatalf("num should be %v, but got %v", cnt, num)
	}

	for i := 0; i < cnt; i++ {
		s, _ := instance.ProposalsIDList(nil, big.NewInt(int64(i)))
		if s != list[i] {
			t.Errorf("expect %v, but got %v", list[i], s)
		}
	}

}

func TestSetAmountThreshold(t *testing.T) {
	backend := initBackend()
	_, instance := initContracts(backend)

	opts := bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)
	value := big.NewInt(0).Mul(big.NewInt(1), big.NewInt(int64(configs.Cpc)))
	if _, err := instance.SetAmountThreshold(opts, value); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	amount, _ := instance.AmountThreshold(nil)
	if amount.Cmp(value) != 0 {
		t.Fatalf("expect %v, but got %v", value, amount)
	}

}

func TestSetApprovalThreshold(t *testing.T) {
	backend := initBackend()
	_, instance := initContracts(backend)

	opts := bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)
	value := big.NewInt(1)
	if _, err := instance.SetApprovalThreshold(opts, value); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	approval, _ := instance.ApprovalThreshold(nil)
	if approval.Cmp(value) != 0 {
		t.Fatalf("expect %v, but got %v", value, approval)
	}

}

func TestSetVoteThreshold(t *testing.T) {
	backend := initBackend()
	_, instance := initContracts(backend)

	opts := bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)
	value := uint16(30)
	if _, err := instance.SetVoteThreshold(opts, value); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	vote, _ := instance.VoteThreshold(nil)
	if vote != value {
		t.Fatalf("expect %v, but got %v", value, vote)
	}

}

func TestSetMaxIDLength(t *testing.T) {
	backend := initBackend()
	_, instance := initContracts(backend)

	opts := bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)
	value := uint16(30)
	if _, err := instance.SetIDLength(opts, value); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	after, _ := instance.IdLength(nil)
	if after != value {
		t.Fatalf("expect %v, but got %v", value, after)
	}
}

func TestSetPeriod(t *testing.T) {
	backend := initBackend()
	_, instance := initContracts(backend)

	opts := bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)
	value := big.NewInt(30)
	if _, err := instance.SetMaxPeriod(opts, value); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	after, _ := instance.MaxPeriod(nil)
	if after.Cmp(value) != 0 {
		t.Fatalf("expect %v, but got %v", value, after)
	}
}

func TestEnableAndDisable(t *testing.T) {
	backend := initBackend()
	_, instance := initContracts(backend)

	opts := bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.DisableContract(opts); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	after, _ := instance.Enabled(nil)
	if after {
		t.Fatalf("expect %v, but got %v", false, after)
	}

	if _, err := instance.EnableContract(opts); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	after, _ = instance.Enabled(nil)
	if !after {
		t.Fatalf("expect %v, but got %v", true, after)
	}
}

func TestRefund(t *testing.T) {
	// refund money
	var (
		id = uuid
	)
	// init
	backend := initBackend()
	_, instance := initContracts(backend)

	// submit a proposal
	submitProposal(t, backend, instance, id)

	// refund with a wrong key
	opts := bind.NewKeyedTransactor(bankKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.Refund(opts, id); err == nil {
		t.Error("This transaction should be fail because the key is not the owner")
	}
	backend.Commit()

	amountThreshold, _ := instance.AmountThreshold(nil)

	if amount, err := instance.GetLockedAmount(nil, id); err != nil {
		t.Error(err)
	} else {
		if amount.Cmp(amountThreshold) != 0 {
			t.Errorf("Expect amount is %v, but got %v", 0, amount)
		}
	}

	// get the balance of bank-key before refund
	balanceBeforeRefund := getBalance(backend, bankAddr)

	// refund
	opts = bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.Refund(opts, id); err != nil {
		t.Errorf("refund should success, but got %v", err)
	}
	backend.Commit()

	// get the balance of bank-key after refund
	balanceAfterBalance := getBalance(backend, bankAddr)

	tmpBalance := big.NewInt(0).Add(balanceBeforeRefund, amountThreshold)

	if tmpBalance.Cmp(balanceAfterBalance) != 0 {
		t.Fatalf(`The balance is wrong, before refund: %v, 
		amountThreshold: %v,
		the sum of those three is %v, 
		but the balance of after refund is %v`, balanceBeforeRefund,
			amountThreshold, tmpBalance, balanceAfterBalance)
	}

	// make the proposal be timeout
	backend.AdjustTime(1000 * time.Second)
	backend.Commit()

	if _, err := instance.CheckTimeout(opts, id); err != nil {
		t.Fatalf("timeout trigger should success, but got %v", err)
	}

	backend.Commit()

	// check if the status is timeout
	checkStatus(t, instance, id, 3)

	// withdrawal should fail
	opts = bind.NewKeyedTransactor(bankKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.Withdraw(opts, id); err == nil {
		t.Fatal("withdrawal should fail because the deposit had been refunded.")
	}
	backend.Commit()

	if amount, err := instance.GetLockedAmount(nil, id); err != nil {
		t.Error(err)
	} else {
		if amount.Cmp(big.NewInt(0)) != 0 {
			t.Errorf("Expect amount is %v, but got %v", 0, amount)
		}
	}
}

func TestRefundAll(t *testing.T) {
	var (
		cnt = 10
	)
	backend := initBackend()
	_, instance := initContracts(backend)

	r := rand.New(rand.NewSource(0))

	var list []string

	// generate 10 keys
	keys := initKeys(t, backend, cnt)

	for i := 0; i < cnt; i++ {
		tmp := randString(r, 36)
		list = append(list, tmp)
		submitProposalWithKey(t, backend, instance, tmp, keys[i])
	}

	num, _ := instance.GetProposalsCnt(nil)

	if num.Cmp(big.NewInt(int64(cnt))) != 0 {
		t.Fatalf("num should be %v, but got %v", cnt, num)
	}

	for i := 0; i < cnt; i++ {
		s, _ := instance.ProposalsIDList(nil, big.NewInt(int64(i)))
		if s != list[i] {
			t.Errorf("expect %v, but got %v", list[i], s)
		}
	}

	// refund with a wrong key
	opts := bind.NewKeyedTransactor(bankKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.RefundAll(opts); err == nil {
		t.Error("This transaction should be fail because the key is not the owner")
	}
	backend.Commit()

	// refundAll when enabled is true, this transaction should fail
	opts = bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.RefundAll(opts); err == nil {
		t.Error("refundAll when enabled is true, this transaction should fail")
	}
	backend.Commit()

	// disable
	opts = bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.DisableContract(opts); err != nil {
		t.Errorf("DisableContract should success but got %v", err)
	}
	backend.Commit()

	// get balance of all keys before refundAll
	var balances []*big.Int
	for i := 0; i < cnt; i++ {
		balance := getBalance(backend, crypto.PubkeyToAddress(keys[i].PublicKey))
		balances = append(balances, balance)
	}

	// refundAll
	opts = bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.RefundAll(opts); err != nil {
		t.Errorf("refundAll should success but got %v", err)
	}
	backend.Commit()

	amountThreshold, _ := instance.AmountThreshold(nil)

	for i := 0; i < cnt; i++ {
		// confirm the lockedAmount of all proposals
		amount, _ := instance.GetLockedAmount(nil, list[i])
		if amount.Cmp(big.NewInt(0)) != 0 {
			t.Errorf("The proposal %v, which id is %v, still locked %v", i, list[i], amount)
		}
		// confirm the balance of those keys
		balance := getBalance(backend, crypto.PubkeyToAddress(keys[i].PublicKey))
		tmpBalance := big.NewInt(0).Add(balances[i], amountThreshold)
		if balance.Cmp(tmpBalance) != 0 {
			t.Errorf("expect balance is %v, but got %v", tmpBalance, balance)
		}
	}

}

func TestRefundAfterApproved(t *testing.T) {
	var (
		cnt = 10
		id  = uuid
	)
	backend := initBackend()
	congressIns, instance := initContracts(backend)
	// generate 10 keys
	keys := initKeys(t, backend, cnt)

	// init congress, add all keys to congress
	initCongress(t, backend, congressIns, keys)

	submitProposal(t, backend, instance, id)

	checkStatus(t, instance, id, 0)

	// update threshold
	updateApprovalThreshold(t, backend, instance, cnt)
	updateVoteThreshold(t, backend, instance, 30)

	// approve all
	approveAll(t, backend, instance, id, keys)

	checkApprovalCnt(t, instance, id, int64(cnt))

	checkStatus(t, instance, id, 1)

	// check if the contract refunded, should not
	// check deposit first
	if amount, _ := instance.GetLockedAmount(nil, id); amount.Cmp(amountThreshold) != 0 {
		t.Fatalf("expect deposited money to %v, but got %v", amountThreshold, amount)
	}

}

func TestRefundAfterVoted(t *testing.T) {
	var (
		cnt = 10
		id  = uuid
	)
	backend := initBackend()
	congressIns, instance := initContracts(backend)
	// generate 10 keys
	keys := initKeys(t, backend, cnt)

	// init congress, add all keys to congress
	initCongress(t, backend, congressIns, keys)

	submitProposal(t, backend, instance, id)

	checkStatus(t, instance, id, 0)

	// update threshold
	updateApprovalThreshold(t, backend, instance, cnt)
	updateVoteThreshold(t, backend, instance, 30)

	// approve all
	approveAll(t, backend, instance, id, keys)

	checkApprovalCnt(t, instance, id, int64(cnt))

	checkStatus(t, instance, id, 1)

	// get the balance of bank-key before refund
	balanceBefore := getBalance(backend, bankAddr)

	voteAll(t, backend, instance, id, keys)

	checkStatus(t, instance, id, 2)

	// check if the contract refunded
	// check deposit first
	if amount, _ := instance.GetLockedAmount(nil, id); amount.Cmp(big.NewInt(0)) != 0 {
		t.Fatalf("expect deposited money to 0, but got %v", amount)
	}

	balanceAfter := getBalance(backend, bankAddr)
	amount := big.NewInt(0).Add(balanceBefore, amountThreshold)

	if amount.Cmp(balanceAfter) != 0 {
		t.Fatalf("balance is wrong, refund failed. Before: %v, After %v, threshold is %v",
			balanceBefore, balanceAfter, amountThreshold)
	}

}

func TestRefundAfterTimeout(t *testing.T) {
	var (
		cnt = 10
		id  = uuid
	)
	backend := initBackend()
	congressIns, instance := initContracts(backend)
	// generate 10 keys
	keys := initKeys(t, backend, cnt)

	// init congress, add all keys to congress
	initCongress(t, backend, congressIns, keys)

	submitProposal(t, backend, instance, id)

	checkStatus(t, instance, id, 0)

	// update threshold
	updateApprovalThreshold(t, backend, instance, cnt)
	updateVoteThreshold(t, backend, instance, 30)

	// approve all
	approveAll(t, backend, instance, id, keys)

	checkApprovalCnt(t, instance, id, int64(cnt))

	checkStatus(t, instance, id, 1)

	// get the balance of bank-key before refund
	balanceBefore := getBalance(backend, bankAddr)

	// make proposal be timeout
	backend.AdjustTime(1000 * time.Second)
	backend.Commit()

	opts := bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)
	if _, err := instance.CheckTimeout(opts, id); err != nil {
		t.Fatal(err)
	}
	backend.Commit()

	checkStatus(t, instance, id, 3)

	// check if the contract refunded
	// check deposit first
	if amount, _ := instance.GetLockedAmount(nil, id); amount.Cmp(big.NewInt(0)) != 0 {
		t.Fatalf("expect deposited money to 0, but got %v", amount)
	}

	balanceAfter := getBalance(backend, bankAddr)
	amount := big.NewInt(0).Add(balanceBefore, amountThreshold)

	if amount.Cmp(balanceAfter) != 0 {
		t.Fatalf("balance is wrong, refund failed. Before: %v, After %v, threshold is %v",
			balanceBefore, balanceAfter, amountThreshold)
	}

}

func randString(r *rand.Rand, len int) string {
	bytes := make([]byte, len)
	for i := 0; i < len; i++ {
		b := r.Intn(26) + 65
		bytes[i] = byte(b)
	}
	return string(bytes)
}

func getBalance(backend *backends.SimulatedBackend, addr common.Address) *big.Int {
	amount, _ := backend.BalanceAt(context.Background(), addr, backend.Blockchain().CurrentBlock().Number())
	return amount
}

func initKeys(t *testing.T, backend *backends.SimulatedBackend, keyCnt int) []*ecdsa.PrivateKey {
	var keys []*ecdsa.PrivateKey
	nonce, _ := backend.NonceAt(context.Background(), bankAddr, backend.Blockchain().CurrentBlock().Number())
	for i := 0; i < keyCnt; i++ {
		key, _ := crypto.GenerateKey()
		keys = append(keys, key)
		if err := transfer(backend, crypto.PubkeyToAddress(key.PublicKey), nonce+uint64(i), 210000); err != nil {
			t.Error(err)
		}
	}
	return keys
}

func initCongress(t *testing.T, backend *backends.SimulatedBackend, instance *congress.Congress, keys []*ecdsa.PrivateKey) {
	for i, key := range keys {
		opts := bind.NewKeyedTransactor(key)
		opts.Value = new(big.Int).Mul(big.NewInt(200000), big.NewInt(configs.Cpc))
		if _, err := instance.JoinCongress(opts, big.NewInt(1)); err != nil {
			t.Error(i, err)
		}
	}
	backend.Commit()
}

func checkCongressNum(t *testing.T, instance *congress.Congress, expect int) {
	// check the nums in congress
	num, _ := instance.GetCongressNum(nil)
	if num.Cmp(big.NewInt(int64(expect))) != 0 {
		t.Errorf("nums in congress should be %v, but got %v", expect, num)
	}
}

func updateApprovalThreshold(t *testing.T, backend *backends.SimulatedBackend, instance *proposal.Proposal, threshold int) {
	opts := bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)

	if _, err := instance.SetApprovalThreshold(opts, big.NewInt(int64(threshold))); err != nil {
		t.Error(err)
	}

	backend.Commit()
}

func updateVoteThreshold(t *testing.T, backend *backends.SimulatedBackend, instance *proposal.Proposal, threshold int) {
	opts := bind.NewKeyedTransactor(ownerKey)
	opts.Value = big.NewInt(0)

	if _, err := instance.SetVoteThreshold(opts, uint16(threshold)); err != nil {
		t.Error(err)
	}

	backend.Commit()
}

func submitProposal(t *testing.T, backend *backends.SimulatedBackend, instance *proposal.Proposal, id string) {
	opts := bind.NewKeyedTransactor(bankKey)
	opts.Value = amountThreshold

	if _, err := instance.Submit(opts, id, periodBase); err != nil {
		t.Fatal(err)
	}
	backend.Commit()
}

func submitProposalWithKey(t *testing.T, backend *backends.SimulatedBackend, instance *proposal.Proposal, id string, key *ecdsa.PrivateKey) {
	opts := bind.NewKeyedTransactor(key)
	opts.Value = amountThreshold

	if _, err := instance.Submit(opts, id, periodBase); err != nil {
		t.Fatal(err)
	}
	backend.Commit()
}

func approveAll(t *testing.T, backend *backends.SimulatedBackend, instance *proposal.Proposal, id string, keys []*ecdsa.PrivateKey) {
	for i, key := range keys {
		opts := bind.NewKeyedTransactor(key)
		opts.Value = big.NewInt(0)
		if _, err := instance.Approval(opts, id); err != nil {
			t.Error(i, err)
		}
	}
	backend.Commit()
}

func voteAll(t *testing.T, backend *backends.SimulatedBackend, instance *proposal.Proposal, id string, keys []*ecdsa.PrivateKey) {
	for i, key := range keys {
		opts := bind.NewKeyedTransactor(key)
		opts.Value = big.NewInt(0)
		if _, err := instance.Vote(opts, id); err != nil {
			t.Error(i, err)
		}
	}
	backend.Commit()
}

func vote(t *testing.T, backend *backends.SimulatedBackend, instance *proposal.Proposal, id string, key *ecdsa.PrivateKey) error {
	opts := bind.NewKeyedTransactor(key)
	opts.Value = big.NewInt(0)
	if _, err := instance.Vote(opts, id); err != nil {
		return err
	}
	backend.Commit()
	return nil
}

func approve(t *testing.T, backend *backends.SimulatedBackend, instance *proposal.Proposal, id string, key *ecdsa.PrivateKey) error {
	opts := bind.NewKeyedTransactor(key)
	opts.Value = big.NewInt(0)
	if _, err := instance.Approval(opts, id); err != nil {
		return err
	}
	backend.Commit()
	return nil
}

func TestTransfer(t *testing.T) {
	backend := initBackend()
	key, _ := crypto.GenerateKey()

	if err := transfer(backend, crypto.PubkeyToAddress(key.PublicKey), 0, 100); err != nil {
		t.Error(err)
	}
	backend.Commit()
}

func transfer(backend *backends.SimulatedBackend, addr common.Address, nonce uint64, cpc int64) error {
	amount := new(big.Int).Mul(big.NewInt(cpc), big.NewInt(configs.Cpc))
	gasLimit := uint64(1000000)
	gasPrice := big.NewInt(10000)

	tx := types.NewTransaction(nonce, addr, amount, gasLimit, gasPrice, nil)
	tx, _ = types.SignTx(tx, types.NewCep1Signer(big.NewInt(configs.MainnetChainId)), bankKey)

	return backend.SendTransaction(context.Background(), tx)
}

func checkProposalCnt(t *testing.T, instance *proposal.Proposal, expect int64) {
	if cnt, err := instance.GetProposalsCnt(nil); err != nil {
		t.Error(err)
	} else {
		if cnt.Cmp(big.NewInt(expect)) != 0 {
			t.Errorf("proposal's length should be %v, but got %v", expect, cnt)
		}
	}
}

func checkApprovalCnt(t *testing.T, instance *proposal.Proposal, id string, expect int64) {
	if cnt, err := instance.GetApprovalCnt(nil, id); err != nil {
		t.Error(err)
	} else {
		if cnt.Cmp(big.NewInt(expect)) != 0 {
			t.Errorf("approval's count should be %v, but got %v", expect, cnt)
		}
	}
}

func checkVoteCnt(t *testing.T, instance *proposal.Proposal, id string, expect int64) {
	if cnt, err := instance.GetVoteCnt(nil, id); err != nil {
		t.Error(err)
	} else {
		if cnt.Cmp(big.NewInt(expect)) != 0 {
			t.Errorf("vote's count should be %v, but got %v", expect, cnt)
		}
	}
}

func checkID(t *testing.T, instance *proposal.Proposal, index int64, id string) {
	if _id, err := instance.ProposalsIDList(nil, big.NewInt(index)); err != nil {
		t.Error(err)
	} else {
		if _id != id {
			t.Errorf("_id %vstored in chain is not equal to %v", _id, id)
		}
	}
}

func checkStatus(t *testing.T, instance *proposal.Proposal, id string, expect uint8) {
	if status, err := instance.GetStatus(nil, id); err == nil {
		if status != expect {
			t.Fatalf("status of this proposal should be %v, but got %v", expect, status)
		}
	} else {
		t.Error(err)
	}
}
