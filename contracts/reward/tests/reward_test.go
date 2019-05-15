package tests

import (
	"context"
	"crypto/ecdsa"
	"fmt"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/types"

	"bitbucket.org/cpchain/chain/configs"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/reward"
	"bitbucket.org/cpchain/chain/core"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	ownerKey, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	ownerAddr   = crypto.PubkeyToAddress(ownerKey.PublicKey)

	candidateKey, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f292")
	candidateAddr   = crypto.PubkeyToAddress(candidateKey.PublicKey)

	participantKey, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f293")
	participantAddr   = crypto.PubkeyToAddress(participantKey.PublicKey)
)

func deploy(prvKey *ecdsa.PrivateKey, backend *backends.SimulatedBackend) (common.Address, *reward.Reward) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	add, _, instance, err := reward.DeployReward(deployTransactor, backend)
	if err != nil {
		log.Fatal("DeployReward is error :", "error is", err)
	}
	return add, instance

}

func TestReward(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{ownerAddr: {Balance: big.NewInt(1000000000000)},
		candidateAddr:   {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		participantAddr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// Start the first quarter of investment
	fmt.Println("unlock contract")
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerTransactOpts.GasLimit = uint64(5000000)
	instance.SetPeriod(ownerTransactOpts, big.NewInt(0)) // set round period is 0
	instance.NewRaise(ownerTransactOpts)

	// initialization a candidate and join the investment
	candidateTransacOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransacOpts.Value = candidateInvest
	candidateTransacOpts.GasLimit = uint64(20000000)
	_, err := instance.SubmitDeposit(candidateTransacOpts)
	if err != nil {
		t.Fatal("Candidate SubmitDeposit is error ", "error is :", err)
	}
	contractBackend.Commit()
	balance, err := instance.GetTotalBalance(nil, candidateAddr)
	fmt.Println("**********************************Total balance is :", "balance", balance)
	if balance.Cmp(candidateInvest) != 0 {
		t.Error("total balance is wrong")
	}
	verifyDeposit(t, candidateInvest, big.NewInt(0), instance, candidateAddr, "candidate")

	// initialization a participant and join the investment
	participantTransacOpts := bind.NewKeyedTransactor(participantKey)
	participantInvest := new(big.Int).Mul(big.NewInt(20000), big.NewInt(1e+18))
	participantTransacOpts.Value = participantInvest
	participantTransacOpts.GasLimit = uint64(20000000)
	_, err = instance.SubmitDeposit(participantTransacOpts)
	if err != nil {
		t.Fatal("Participant SubmitDeposit is error ", "error is :", err)
	}
	contractBackend.Commit()
	balance2, err := instance.GetTotalBalance(nil, participantAddr)
	fmt.Println("**********************************Total balance is :", "balance", balance2)
	verifyDeposit(t, participantInvest, big.NewInt(0), instance, participantAddr, "participant")

	_, err = instance.StartNewRound(ownerTransactOpts)
	if err != nil {
		t.Fatal("Participant StartNewRound is error ", "error is :", err)
	}
	contractBackend.Commit()
	locked, err := instance.IsLocked(nil)
	if locked != true {
		log.Fatal("the locked status should be true after new round started")
	}

	verifyDeposit(t, big.NewInt(0), candidateInvest, instance, candidateAddr, "candidate after new round")
	verifyDeposit(t, big.NewInt(0), participantInvest, instance, participantAddr, "participant after new round")

	trans, _ := instance.SubmitDeposit(participantTransacOpts)
	contractBackend.Commit()
	receipt, _ := contractBackend.TransactionReceipt(context.Background(), trans.Hash())
	if receipt.Status != types.ReceiptStatusFailed {
		t.Error("the transaction should fail because it is in locked period")
	}
	verifyDeposit(t, big.NewInt(0), participantInvest, instance, participantAddr, "participant cannot invest more during locked period")

	// start the second quarter of investment
	_, err = instance.NewRaise(ownerTransactOpts)
	if err != nil {
		t.Fatal(" NewRaise is error ", "error is :", err)
	}
	contractBackend.Commit()

	locked, err = instance.IsLocked(nil)
	if locked == true {
		log.Error("the locked status should be false after new raise started")
	}

	participantTransacOpts.Value = big.NewInt(0)
	trans, err = instance.WantRenew(participantTransacOpts)
	if err != nil {
		t.Fatal("Participant WantRenew is error ", "error", err)
	}

	candidateTransacOpts.Value = big.NewInt(0)
	trans, err = instance.QuitRenew(candidateTransacOpts)
	if err != nil {
		t.Fatal("Candidate QuitRenew is error", "error", err)
	}

	contractBackend.Commit()

	receipt, _ = contractBackend.TransactionReceipt(context.Background(), trans.Hash())

	c, _ := instance.IsToRenew(nil, participantAddr)
	if c != true {
		t.Fatal("the participant's investment should be set to renew")
	}

	c, _ = instance.IsToRenew(nil, candidateAddr)
	if c != false {
		t.Fatal("the candidate's investment should NOT be set to renew")
	}

	_, err = instance.StartNewRound(ownerTransactOpts)
	contractBackend.Commit()

	r, _ := instance.NextRound(nil)
	t.Log("next round", r.String())

	bonus := new(big.Int).Mul(big.NewInt(1250000), big.NewInt(1e+18))
	total := new(big.Int).Add(participantInvest, candidateInvest)
	participantInterest := new(big.Int).Mul(participantInvest, bonus)
	participantInterest = participantInterest.Div(participantInterest, total)
	candidateInterest := new(big.Int).Mul(candidateInvest, bonus)
	candidateInterest = candidateInterest.Div(candidateInterest, total)

	t.Log(participantInvest.String(), ",", participantInterest.String(), ",", total.String(), ",", bonus.String())

	verifyDeposit(t, participantInterest, participantInvest, instance, participantAddr, "participant after second round")
	verifyDeposit(t, new(big.Int).Add(candidateInterest, candidateInvest), big.NewInt(0), instance, candidateAddr, "candidate after second round")
}

func TestRewardCaller_IsToRenew(t *testing.T) {
	// deploy reward
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{ownerAddr: {Balance: new(big.Int).Mul(big.NewInt(10000000000), big.NewInt(configs.Cpc))},
		candidateAddr:   {Balance: new(big.Int).Mul(big.NewInt(10000000), big.NewInt(configs.Cpc))},
		participantAddr: {Balance: new(big.Int).Mul(big.NewInt(10000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// new raise
	fmt.Println("unlock contract")
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerTransactOpts.GasLimit = uint64(5000000)
	instance.SetPeriod(ownerTransactOpts, big.NewInt(0)) // set round period is 0
	contractBackend.Commit()
	_, err := instance.NewRaise(ownerTransactOpts)
	if err != nil {
		t.Fatal("NewRaise function is error", "error is ", err)
	}
	contractBackend.Commit()

	// submit deposit
	candidateTransacOpts := bind.NewKeyedTransactor(candidateKey)
	candidateTransacOpts.Value = new(big.Int).Mul(big.NewInt(2000000), big.NewInt(configs.Cpc))
	candidateTransacOpts.GasLimit = uint64(5000000)
	_, err = instance.SubmitDeposit(candidateTransacOpts)
	if err != nil {
		t.Fatal("SubmitDeposit is error ", "error is ", err)
	}
	contractBackend.Commit()

	// start new round
	_, err = instance.StartNewRound(ownerTransactOpts)
	if err != nil {
		t.Fatal("SubmitDeposit is error ", "error is ", err)
	}
	contractBackend.Commit()

	// check "is to renew" be true
	renew, err := instance.IsToRenew(nil, candidateAddr)
	if err != nil {
		t.Fatal("IsToRenew is error", "error is ", err)
	}
	if renew != true {
		t.Fatal("wrong renew", "we want :", true, "but get", renew)
	}

	// new raise
	_, err = instance.NewRaise(ownerTransactOpts)
	if err != nil {
		t.Fatal("NewRaise function is error", "error is ", err)
	}
	contractBackend.Commit()

	// set "is to renew" to be false
	candidateTransacOpts.Value = big.NewInt(0)
	_, err = instance.QuitRenew(candidateTransacOpts)
	if err != nil {
		t.Fatal("QuitRenew function is error", "error is ", err)
	}
	contractBackend.Commit()

	// check "is to renew" be false
	renew, err = instance.IsToRenew(nil, candidateAddr)
	if err != nil {
		t.Fatal("IsToRenew is error", "error is ", err)
	}
	if renew != false {
		t.Fatal("wrong renew", "we want:", false, " but get:", renew)
	}

	// submit deposit
	candidateTransacOpts.Value = new(big.Int).Mul(big.NewInt(2000000), big.NewInt(configs.Cpc))
	_, err = instance.SubmitDeposit(candidateTransacOpts)
	if err != nil {
		t.Fatal("SubmitDeposit is error ", "error is ", err)
	}
	contractBackend.Commit()

	// start new round
	_, err = instance.StartNewRound(ownerTransactOpts)
	if err != nil {
		t.Fatal("SubmitDeposit is error ", "error is ", err)
	}
	contractBackend.Commit()

	test, err := instance.IsRNode(nil, candidateAddr)
	if test == false {
		t.Fatal("0000000000000000000")
	}

	// check "is to renew" be true
	renew, err = instance.IsToRenew(nil, candidateAddr)
	if err != nil {
		t.Fatal("IsToRenew is error", "error is ", err)
	}
	if renew != true {
		t.Fatal("wrong renew", "we want :", true, "but get", renew)
	}
}

func verifyDeposit(t *testing.T, freeBalance *big.Int, lockedBalance *big.Int, instance *reward.Reward, address common.Address, when string) {
	fb, err := instance.GetFreeBalance(nil, address)
	if err != nil {
		t.Fatal("GetTempDeposit is error ", "error is :", err)
	}
	if fb.Cmp(freeBalance) != 0 {
		t.Error("freeBalance is error", "we want ", freeBalance.String(), "the result is", fb.String(), "when", when)
	}

	lb, err := instance.GetLockedBalance(nil, address)
	if err != nil {
		t.Fatal("GetLockedDeposit is error ", "error is :", err)
	}
	if lb.Cmp(lockedBalance) != 0 {
		t.Error("lockedBalance is error", "we want ", lockedBalance.String(), "the result is", lb.String(), "when", when)
	}
}
