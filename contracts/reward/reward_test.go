package reward_test

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
	reward "bitbucket.org/cpchain/chain/contracts/reward"
	"bitbucket.org/cpchain/chain/core"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	ownerKey, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	ownerAddr   = crypto.PubkeyToAddress(ownerKey.PublicKey)

	candidateKey, _ = crypto.HexToECDSA("8a1f9a8f95be41cd7ccb6168179afb4504aefe388d1e14474d32c45c72ce7b7a")
	candidateAddr   = crypto.PubkeyToAddress(candidateKey.PublicKey)

	candidate2Key, _ = crypto.HexToECDSA("fad9c8855b740a0b7ed4c221dbad0f33a83a49cad6b3fe8d5817ac83d38b6a19")
	candidate2Addr   = crypto.PubkeyToAddress(candidate2Key.PublicKey)
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
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// Start the first quarter of investment
	fmt.Println("unlock contract")
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerTransactOpts.GasLimit = uint64(5000000)
	instance.SetPeriod(ownerTransactOpts, big.NewInt(0)) // set round period is 0
	instance.NewRaise(ownerTransactOpts)

	// initialization a candidate and join the investment
	candidateTransacOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(20000), big.NewInt(1e+18))
	candidateTransacOpts.Value = candidateInvest
	candidateTransacOpts.GasLimit = uint64(20000000)
	_, err := instance.SubmitDeposit(candidateTransacOpts)
	if err != nil {
		t.Fatal("Candidate SubmitDeposit is error ", "error is :", err)
	}
	contractBackend.Commit()
	balance, err := instance.GetTotalBalanceOf(nil, candidateAddr)
	fmt.Println("**********************************Total balance is :", "balance", balance)
	if balance.Cmp(candidateInvest) != 0 {
		t.Error("total balance is wrong")
	}
	verifyDeposit(t, candidateInvest, big.NewInt(0), instance, candidateAddr, "candidate")

	// initialization a participant and join the investment
	candidate2TransacOpts := bind.NewKeyedTransactor(candidate2Key)
	candidate2Invest := new(big.Int).Mul(big.NewInt(10000), big.NewInt(1e+18))
	candidate2TransacOpts.Value = candidate2Invest
	candidate2TransacOpts.GasLimit = uint64(20000000)
	_, err = instance.SubmitDeposit(candidate2TransacOpts)
	if err != nil {
		t.Fatal("Participant SubmitDeposit is error ", "error is :", err)
	}
	contractBackend.Commit()
	verifyDeposit(t, candidate2Invest, big.NewInt(0), instance, candidate2Addr, "participant")

	_, err = instance.StartNewRound(ownerTransactOpts)
	if err != nil {
		t.Fatal("Participant StartNewRound is error ", "error is :", err)
	}
	contractBackend.Commit()

	r1, _ := instance.NextRound(nil)
	t.Log("next round", r1.String())

	locked, err := instance.Locked(nil)
	if locked != true {
		log.Fatal("the locked status should be true after new round started")
	}

	verifyDeposit(t, big.NewInt(0), candidateInvest, instance, candidateAddr, "candidate after new round")
	verifyDeposit(t, candidate2Invest, big.NewInt(0), instance, candidate2Addr, "participant after new round")

	trans, _ := instance.SubmitDeposit(candidate2TransacOpts)
	contractBackend.Commit()
	receipt, _ := contractBackend.TransactionReceipt(context.Background(), trans.Hash())
	if receipt.Status != types.ReceiptStatusFailed {
		t.Error("the transaction should fail because it is in locked period")
	}
	verifyDeposit(t, candidate2Invest, big.NewInt(0), instance, candidate2Addr, "participant cannot invest more during locked period")

	// start the second quarter of investment
	_, err = instance.NewRaise(ownerTransactOpts)
	if err != nil {
		t.Fatal(" NewRaise is error ", "error is :", err)
	}
	contractBackend.Commit()

	locked, err = instance.Locked(nil)
	if locked == true {
		log.Error("the locked status should be false after new raise started")
	}

	// set bonus
	bonus := new(big.Int).Mul(big.NewInt(10000), big.NewInt(1e+18))
	ownerTransactOpts.Value = bonus
	_, err = instance.SetBonusPool(ownerTransactOpts, bonus)
	contractBackend.Commit()

	bonus2, err := instance.BonusPool(nil)
	if bonus.Cmp(bonus2) != 0 {
		t.Errorf("bouns2 %v should equal to bonus %v", bonus2, bonus)
	}

	ownerTransactOpts.Value = big.NewInt(0)
	_, err = instance.StartNewRound(ownerTransactOpts)
	contractBackend.Commit()

	r, _ := instance.NextRound(nil)
	t.Log("next round", r.String())

	locked, err = instance.Locked(nil)
	if locked != true {
		t.Fatal("the locked status should be true after new round started")
	}

	total := new(big.Int).Add(big.NewInt(0), candidateInvest)
	candidateInterest := new(big.Int).Mul(candidateInvest, bonus)
	candidateInterest = candidateInterest.Div(candidateInterest, total)

	verifyDeposit(t, candidateInterest, candidateInvest, instance, candidateAddr, "candidate after second round")
}

func TestRewardCaller_IsToRenew(t *testing.T) {
	// deploy reward
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{ownerAddr: {Balance: new(big.Int).Mul(big.NewInt(10000000000), big.NewInt(configs.Cpc))},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(10000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(10000000), big.NewInt(configs.Cpc))}})
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

	test, err := instance.IsEnode(nil, candidateAddr)
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

func TestRewardRefundAndRefundAll(t *testing.T) {
	// deploy contract
	baseAccount := new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{ownerAddr: {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: baseAccount},
		candidate2Addr: {Balance: baseAccount}})
	_, instance := deploy(ownerKey, contractBackend)

	// Start the first quarter of investment
	fmt.Println("unlock contract")
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerTransactOpts.GasLimit = uint64(5000000)
	instance.SetPeriod(ownerTransactOpts, big.NewInt(0)) // set round period is 0
	instance.NewRaise(ownerTransactOpts)

	// initialization a candidate and join the investment
	candidateTransacOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(20000), big.NewInt(1e+18))
	candidateTransacOpts.Value = candidateInvest
	candidateTransacOpts.GasLimit = uint64(20000000)
	_, err := instance.SubmitDeposit(candidateTransacOpts)
	if err != nil {
		t.Fatal("Candidate SubmitDeposit is error ", "error is :", err)
	}
	contractBackend.Commit()
	balance, err := instance.GetTotalBalanceOf(nil, candidateAddr)
	if balance.Cmp(candidateInvest) != 0 {
		t.Error("total balance is wrong")
	}
	verifyDeposit(t, candidateInvest, big.NewInt(0), instance, candidateAddr, "candidate")

	// initialization a participant and join the investment
	candidate2TransacOpts := bind.NewKeyedTransactor(candidate2Key)
	candidate2Invest := new(big.Int).Mul(big.NewInt(10000), big.NewInt(1e+18))
	candidate2TransacOpts.Value = candidate2Invest
	candidate2TransacOpts.GasLimit = uint64(20000000)
	_, err = instance.SubmitDeposit(candidate2TransacOpts)
	if err != nil {
		t.Fatal("Participant SubmitDeposit is error ", "error is :", err)
	}
	contractBackend.Commit()

	verifyDeposit(t, candidate2Invest, big.NewInt(0), instance, candidate2Addr, "participant")

	// refund candidate
	// fail
	tx, err := instance.RefundDeposit(ownerTransactOpts, candidateAddr, new(big.Int).Add(candidateInvest, big.NewInt(1)))
	if err != nil {
		t.Error(err)
	}
	contractBackend.Commit()

	receipt, _ := contractBackend.TransactionReceipt(context.Background(), tx.Hash())
	if receipt.Status != types.ReceiptStatusFailed {
		t.Error("the transaction should fail because the _value larger than the account which candiate have")
	}

	// refund candidate
	// success
	_, err = instance.RefundDeposit(ownerTransactOpts, candidateAddr, candidateInvest)
	if err != nil {
		t.Error(err)
	}
	contractBackend.Commit()

	verifyDeposit(t, big.NewInt(0), big.NewInt(0), instance, candidateAddr, "refund freeBalance to candidate")
	verifyDeposit(t, candidate2Invest, big.NewInt(0), instance, candidate2Addr, "not refund to candidate2")

	// refund all
	instance.RefundAll(ownerTransactOpts)
	contractBackend.Commit()

	verifyDeposit(t, big.NewInt(0), big.NewInt(0), instance, candidateAddr, "refund all")
	verifyDeposit(t, big.NewInt(0), big.NewInt(0), instance, candidate2Addr, "refund all")

	state, _ := contractBackend.Blockchain().State()
	balance1 := state.GetBalance(candidateAddr)
	if balance1.Cmp(new(big.Int).Sub(baseAccount, candidateInvest)) <= 0 {
		t.Error("candidate's balance shoule more than base-candiateInvest")
	}

	balance2 := state.GetBalance(candidate2Addr)
	if balance2.Cmp(new(big.Int).Sub(baseAccount, candidate2Invest)) <= 0 {
		t.Error("candidate2's balance shoule more than base-candiate2Invest")
	}

}

func TestSetBonus(t *testing.T) {
	// deploy contract
	baseAccount := new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: baseAccount},
		candidateAddr:  {Balance: baseAccount},
		candidate2Addr: {Balance: baseAccount}})
	_, instance := deploy(ownerKey, contractBackend)

	// Start the first quarter of investment
	fmt.Println("unlock contract")
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerTransactOpts.GasLimit = uint64(5000000)
	instance.SetPeriod(ownerTransactOpts, big.NewInt(0)) // set round period is 0
	instance.NewRaise(ownerTransactOpts)

	// set bouns fail
	bonus := new(big.Int).Mul(big.NewInt(10000), big.NewInt(1e+18))
	ownerTransactOpts.Value = new(big.Int)
	tx, _ := instance.SetBonusPool(ownerTransactOpts, bonus)
	contractBackend.Commit()

	receipt, _ := contractBackend.TransactionReceipt(context.Background(), tx.Hash())
	if receipt.Status != types.ReceiptStatusFailed {
		t.Error("the transaction should fail because the bonus is less than value")
	}

	// set bonus success
	bonus = new(big.Int).Mul(big.NewInt(10000), big.NewInt(1e+18))
	ownerTransactOpts.Value = bonus
	instance.SetBonusPool(ownerTransactOpts, bonus)
	contractBackend.Commit()

	bonus2, _ := instance.BonusPool(nil)
	if bonus.Cmp(bonus2) != 0 {
		t.Errorf("bouns2 %v should equal to bonus %v", bonus2, bonus)
	}
}

func TestWithdraw(t *testing.T) {
	// deploy contract
	baseAccount := new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{ownerAddr: {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: baseAccount},
		candidate2Addr: {Balance: baseAccount}})
	_, instance := deploy(ownerKey, contractBackend)

	// Start the first quarter of investment
	fmt.Println("unlock contract")
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerTransactOpts.GasLimit = uint64(5000000)
	instance.SetPeriod(ownerTransactOpts, big.NewInt(0)) // set round period is 0
	instance.NewRaise(ownerTransactOpts)

	// initialization a candidate and join the investment
	candidateTransacOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(20000), big.NewInt(1e+18))
	candidateTransacOpts.Value = candidateInvest
	candidateTransacOpts.GasLimit = uint64(20000000)
	_, err := instance.SubmitDeposit(candidateTransacOpts)
	if err != nil {
		t.Fatal("Candidate SubmitDeposit is error ", "error is :", err)
	}
	contractBackend.Commit()
	balance, err := instance.GetTotalBalanceOf(nil, candidateAddr)
	if balance.Cmp(candidateInvest) != 0 {
		t.Error("total balance is wrong")
	}
	verifyDeposit(t, candidateInvest, big.NewInt(0), instance, candidateAddr, "candidate")

	// withdraw
	// fail
	candidateTransacOpts.Value = big.NewInt(0)
	withdrawValue := new(big.Int).Mul(big.NewInt(50000), big.NewInt(1e+18))
	tx, _ := instance.Withdraw(candidateTransacOpts, withdrawValue)

	contractBackend.Commit()

	receipt, _ := contractBackend.TransactionReceipt(context.Background(), tx.Hash())
	if receipt.Status != types.ReceiptStatusFailed {
		t.Error("the transaction should fail because the balance is less than value")
	}

	// success
	candidateTransacOpts.Value = big.NewInt(0)
	withdrawValue = new(big.Int).Mul(big.NewInt(5000), big.NewInt(1e+18))
	instance.Withdraw(candidateTransacOpts, withdrawValue)

	contractBackend.Commit()

	verifyDeposit(t, new(big.Int).Sub(candidateInvest, withdrawValue), big.NewInt(0), instance, candidateAddr, "after withdraw")

}

func verifyDeposit(t *testing.T, freeBalance *big.Int, lockedBalance *big.Int, instance *reward.Reward, address common.Address, when string) {
	fb, err := instance.GetFreeBalanceOf(nil, address)
	if err != nil {
		t.Fatal("GetTempDeposit is error ", "error is :", err)
	}
	if fb.Cmp(freeBalance) != 0 {
		t.Error("freeBalance is error", "we want ", freeBalance.String(), "the result is", fb.String(), "when", when)
	}

	lb, err := instance.GetLockedBalanceOf(nil, address)
	if err != nil {
		t.Fatal("GetLockedDeposit is error ", "error is :", err)
	}
	if lb.Cmp(lockedBalance) != 0 {
		t.Error("lockedBalance is error", "we want ", lockedBalance.String(), "the result is", lb.String(), "when", when)
	}
}
