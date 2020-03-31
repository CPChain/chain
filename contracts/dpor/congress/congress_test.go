package congress_test

import (
	"context"
	"crypto/ecdsa"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/configs"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	congress "bitbucket.org/cpchain/chain/contracts/dpor/congress"
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

	initVersion = big.NewInt(1)
	initBalance = new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))
)

func deploy(prvKey *ecdsa.PrivateKey, backend *backends.SimulatedBackend) (common.Address, *congress.Congress) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	addr, _, instance, err := congress.DeployCongress(deployTransactor, backend)
	if err != nil {
		log.Fatal("DeployCongress is error :", "error is", err)
	}
	return addr, instance

}

func TestJoinCongress(t *testing.T) {
	// deploy contract
	ctx := context.Background()
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: initBalance},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	contractAddr, instance := deploy(ownerKey, contractBackend)

	contractBackend.Commit()

	checkCongressNum(t, instance, 0)

	// join congress
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinCongress(candidateTransactOpts, initVersion)
	checkError(t, "join congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, true)

	checkCongressNum(t, instance, 1)

	// check balance of the contract address
	contractBalance, err := contractBackend.BalanceAt(ctx, contractAddr, contractBackend.Blockchain().CurrentBlock().Number())
	checkError(t, "get balance of contractAddr", err)
	if contractBalance.Cmp(candidateInvest) != 0 {
		t.Fatalf("contractBalance %v != candidateInvest %v", contractBalance, candidateInvest)
	}

	// check balance
	currentBlock := contractBackend.Blockchain().CurrentBlock()
	balance, err := contractBackend.BalanceAt(ctx, candidateAddr, currentBlock.Number())
	checkError(t, "get balance of candidateAddr", err)
	// initBalance = candidateInvest + gasUsed + currentBalance
	gasUsed := currentBlock.GasUsed()
	amount := balance.Add(balance, candidateInvest)
	amount = amount.Add(amount, big.NewInt(int64(gasUsed)))
	if initBalance.Cmp(amount) != 0 {
		t.Error("initBalance != candidateInvest + gasUsed + currentBalance")
	}
}

func TestNotEnoughInvest(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join congress
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(100000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest

	_, err := instance.JoinCongress(candidateTransactOpts, initVersion)
	checkError(t, "join congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, false)

	checkCongressNum(t, instance, 0)
}

func TestJoinTwice(t *testing.T) {
	// deploy contract
	ctx := context.Background()
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: initBalance},
		candidate2Addr: {Balance: initBalance}})
	contractAddr, instance := deploy(ownerKey, contractBackend)
	contractBackend.Commit()

	// join congress
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	// once
	_, err := instance.JoinCongress(candidateTransactOpts, initVersion)
	checkError(t, "join congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, true)

	checkCongressNum(t, instance, 1)

	gasUsed1 := contractBackend.Blockchain().CurrentBlock().GasUsed()

	balance1, err := contractBackend.BalanceAt(ctx, candidateAddr, contractBackend.Blockchain().CurrentBlock().Number())
	checkError(t, "get balance of candidateAddr", err)

	amount := big.NewInt(0).Add(balance1, big.NewInt(int64(gasUsed1)))
	amount.Add(amount, candidateInvest)
	if initBalance.Cmp(amount) != 0 {
		t.Error("initBalance != candidateInvest + gasUsed + currentBalance")
	}

	// twice
	_, err = instance.JoinCongress(candidateTransactOpts, initVersion)
	checkError(t, "join congress", err)
	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, true)

	checkCongressNum(t, instance, 1)

	// check balance of the contract address
	contractBalance, err := contractBackend.BalanceAt(ctx, contractAddr, contractBackend.Blockchain().CurrentBlock().Number())
	checkError(t, "get balance of contractAddr", err)
	if contractBalance.Cmp(candidateInvest) != 0 {
		t.Fatalf("contractBalance %v != candidateInvest %v", contractBalance, candidateInvest)
	}

	// check balance
	balance2, err := contractBackend.BalanceAt(ctx, candidateAddr, contractBackend.Blockchain().CurrentBlock().Number())
	checkError(t, "get balance of candidateAddr", err)
	// balance1 = balance2 + gasUsed
	gasUsed2 := contractBackend.Blockchain().CurrentBlock().GasUsed()
	amount = big.NewInt(0).Add(balance2, big.NewInt(int64(gasUsed2)))
	if balance1.Cmp(amount) != 0 {
		t.Error("balance1 = balance2 + gasUsed")
	}
}

func TestMultiMembers(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join congress
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinCongress(candidateTransactOpts, initVersion)
	checkError(t, "join congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, true)

	checkCongressNum(t, instance, 1)

	candidate2TransactOpts := bind.NewKeyedTransactor(candidate2Key)
	candidate2Invest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidate2TransactOpts.GasLimit = uint64(50000000)
	candidate2TransactOpts.Value = candidate2Invest
	_, err = instance.JoinCongress(candidate2TransactOpts, initVersion)
	checkError(t, "join congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidate2Addr, true)

	checkCongressNum(t, instance, 2)

	// get all members in congress
	addrs, err := instance.GetCongress(nil)
	checkError(t, "get all rnodes", err)
	if addrs[0] != candidateAddr {
		t.Error("members 1 is not candidate 1")
	}
	if addrs[1] != candidate2Addr {
		t.Error("members 2 is not candidate 2")
	}
}

func TestQuitWithinPeriod(t *testing.T) {
	// deploy contract
	ctx := context.Background()
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	contractAddr, instance := deploy(ownerKey, contractBackend)

	// join congress
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinCongress(candidateTransactOpts, initVersion)
	checkError(t, "join congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, true)

	checkCongressNum(t, instance, 1)

	// quit congress within period
	candidateTransactOpts = bind.NewKeyedTransactor(candidateKey)
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	_, err = instance.QuitCongress(candidateTransactOpts)
	checkError(t, "quit congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, true)

	checkCongressNum(t, instance, 1)

	// check balance of the contract address
	contractBalance, err := contractBackend.BalanceAt(ctx, contractAddr, contractBackend.Blockchain().CurrentBlock().Number())
	checkError(t, "get balance of contractAddr", err)
	if contractBalance.Cmp(candidateInvest) != 0 {
		t.Fatalf("contractBalance %v != candidateInvest %v", contractBalance, candidateInvest)
	}

	// set period to 0
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerTransactOpts.GasLimit = uint64(50000000)
	ownerTransactOpts.Value = new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	_, err = instance.SetPeriod(ownerTransactOpts, new(big.Int).SetInt64(0))

	contractBackend.Commit()

	// quit again
	candidateTransactOpts = bind.NewKeyedTransactor(candidateKey)
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	_, err = instance.QuitCongress(candidateTransactOpts)
	checkError(t, "quit congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, false)

	checkCongressNum(t, instance, 0)

	// check balance of the contract address
	contractBalance, err = contractBackend.BalanceAt(ctx, contractAddr, contractBackend.Blockchain().CurrentBlock().Number())
	checkError(t, "get balance of contractAddr", err)
	if contractBalance.Cmp(big.NewInt(0)) != 0 {
		t.Fatalf("contractBalance %v != 0", contractBalance)
	}

}

func TestJoinCongressAndQuit(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join congress
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinCongress(candidateTransactOpts, initVersion)
	checkError(t, "join congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, true)

	checkCongressNum(t, instance, 1)

	// set period = 0
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerInvest := new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	ownerTransactOpts.GasLimit = uint64(50000000)
	ownerTransactOpts.Value = ownerInvest
	_, err = instance.SetPeriod(ownerTransactOpts, new(big.Int).SetInt64(0))

	contractBackend.Commit()

	// get period
	period, err := instance.Period(nil)
	if period.Cmp(big.NewInt(0)) != 0 {
		t.Fatalf("period is error. %v != %v", period, 0)
	}

	// quit congress
	candidateTransactOpts = bind.NewKeyedTransactor(candidateKey)
	candidateInvest = new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err = instance.QuitCongress(candidateTransactOpts)
	checkError(t, "quit congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, false)

	checkCongressNum(t, instance, 0)
}

func TestThreshold(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join congress
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinCongress(candidateTransactOpts, initVersion)
	checkError(t, "join congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, true)

	checkCongressNum(t, instance, 1)

	// set threshold = 1
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerInvest := new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	ownerTransactOpts.GasLimit = uint64(50000000)
	ownerTransactOpts.Value = ownerInvest

	newThreshold := new(big.Int).Mul(big.NewInt(3000000), big.NewInt(1e+18))
	_, err = instance.SetCongressThreshold(ownerTransactOpts, newThreshold)
	checkError(t, "set rnode threshold", err)

	contractBackend.Commit()

	// get threshold
	threshold, err := instance.CongressThreshold(nil)
	checkError(t, "get threshold", err)
	if threshold.Cmp(newThreshold) != 0 {
		t.Fatalf("threshold error! %d != %d", threshold, newThreshold)
	}

	// join congress
	candidate2TransactOpts := bind.NewKeyedTransactor(candidate2Key)
	candidate2Invest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidate2TransactOpts.GasLimit = uint64(50000000)
	candidate2TransactOpts.Value = candidate2Invest
	_, err = instance.JoinCongress(candidate2TransactOpts, initVersion)
	checkError(t, "join congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidate2Addr, false)

	checkCongressNum(t, instance, 1)
}

func TestCongressEnableAndDisable(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// set contract enable = false
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerInvest := new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	ownerTransactOpts.GasLimit = uint64(50000000)
	ownerTransactOpts.Value = ownerInvest

	_, err := instance.DisableContract(ownerTransactOpts)
	checkError(t, "set contract disabled", err)

	contractBackend.Commit()

	checkEnabled(t, instance, false)

	// enable contract
	_, err = instance.EnableContract(ownerTransactOpts)
	checkError(t, "set contract enabled", err)

	contractBackend.Commit()

	checkEnabled(t, instance, true)
}

func TestSupportedVersion(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join congress
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinCongress(candidateTransactOpts, initVersion)
	checkError(t, "join congress", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, true)

	checkCongressNum(t, instance, 1)

	// set supportedVersion to 2
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerInvest := new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	ownerTransactOpts.GasLimit = uint64(50000000)
	ownerTransactOpts.Value = ownerInvest

	secondVersion := big.NewInt(2)
	_, err = instance.SetSupportedVersion(ownerTransactOpts, secondVersion)
	checkError(t, "set supported version", err)

	contractBackend.Commit()

	// join congress with initVersion
	candidate2TransactOpts := bind.NewKeyedTransactor(candidate2Key)
	candidate2Invest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidate2TransactOpts.GasLimit = uint64(50000000)
	candidate2TransactOpts.Value = candidate2Invest
	_, err = instance.JoinCongress(candidate2TransactOpts, initVersion)
	checkError(t, "join congress with init version", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidate2Addr, false)

	checkCongressNum(t, instance, 1)

	// join congress with secondVersion
	_, err = instance.JoinCongress(candidate2TransactOpts, secondVersion)
	checkError(t, "join congress with second version", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidate2Addr, true)

	checkCongressNum(t, instance, 2)
}

func TestRefund(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// get balance
	state, err := contractBackend.Blockchain().State()
	checkError(t, "get state", err)

	amount1 := state.GetBalance(candidateAddr)

	// join congress
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err = instance.JoinCongress(candidateTransactOpts, initVersion)
	checkError(t, "join congress", err)

	contractBackend.Commit()

	state, err = contractBackend.Blockchain().State()

	amount2 := state.GetBalance(candidateAddr)

	if amount2.Cmp(amount1) >= 0 || new(big.Int).Add(amount2, candidateInvest).Cmp(amount1) >= 0 {
		t.Fatalf("balance error amount1: %v, amount2 + invest: %v", amount1, new(big.Int).Add(amount2, candidateInvest))
	}

	checkIsInCongress(t, instance, candidateAddr, true)

	checkCongressNum(t, instance, 1)

	// refund
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerInvest := new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	ownerTransactOpts.GasLimit = uint64(50000000)
	ownerTransactOpts.Value = ownerInvest

	_, err = instance.Refund(ownerTransactOpts, candidateAddr)
	checkError(t, "refund", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, false)

	checkCongressNum(t, instance, 0)

	state, err = contractBackend.Blockchain().State()

	amount3 := state.GetBalance(candidateAddr)
	if amount3.Cmp(amount2) <= 0 {
		t.Fatalf("amount3 %v <= amount2 %v", amount3, amount2)
	}
}

func TestRefundAll(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// get balance
	state, err := contractBackend.Blockchain().State()
	checkError(t, "get state", err)

	amount1 := state.GetBalance(candidateAddr)

	// join congress
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err = instance.JoinCongress(candidateTransactOpts, initVersion)
	checkError(t, "join congress", err)

	contractBackend.Commit()

	state, err = contractBackend.Blockchain().State()

	amount2 := state.GetBalance(candidateAddr)

	if amount2.Cmp(amount1) >= 0 || new(big.Int).Add(amount2, candidateInvest).Cmp(amount1) >= 0 {
		t.Fatalf("balance error amount1: %v, amount2 + invest: %v", amount1, new(big.Int).Add(amount2, candidateInvest))
	}

	checkIsInCongress(t, instance, candidateAddr, true)

	checkCongressNum(t, instance, 1)

	// refund all
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerInvest := new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	ownerTransactOpts.GasLimit = uint64(50000000)
	ownerTransactOpts.Value = ownerInvest

	_, err = instance.RefundAll(ownerTransactOpts)
	checkError(t, "refund", err)

	contractBackend.Commit()

	checkIsInCongress(t, instance, candidateAddr, false)

	checkCongressNum(t, instance, 0)

	state, err = contractBackend.Blockchain().State()

	amount3 := state.GetBalance(candidateAddr)
	if amount3.Cmp(amount2) <= 0 {
		t.Fatalf("amount3 %v <= amount2 %v", amount3, amount2)
	}
}

func checkError(t *testing.T, title string, err error) {
	if err != nil {
		t.Fatal(title, ":", err)
	}
}

func checkIsInCongress(t *testing.T, instance *congress.Congress, addr common.Address, expect bool) {
	isInCongress, err := instance.IsInCongress(nil, addr)
	checkError(t, "is in congress", err)
	if isInCongress != expect {
		t.Errorf("rnode check %v != %v", isInCongress, expect)
	}
}

func checkCongressNum(t *testing.T, instance *congress.Congress, amount int) {
	num, err := instance.GetCongressNum(nil)
	checkError(t, "get congress num", err)

	if num.Cmp(new(big.Int).SetInt64(int64(amount))) != 0 {
		t.Errorf("members'num %d != %d", num, amount)
	}
}

func checkEnabled(t *testing.T, instance *congress.Congress, expect bool) {
	enabled, err := instance.Enabled(nil)
	checkError(t, "check enabled", err)

	if enabled != expect {
		t.Errorf("members'num %v != %v", enabled, expect)
	}
}
