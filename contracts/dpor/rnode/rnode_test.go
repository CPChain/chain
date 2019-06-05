package rnode_test

import (
	"crypto/ecdsa"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/configs"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	rnode "bitbucket.org/cpchain/chain/contracts/dpor/rnode"
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
)

func deploy(prvKey *ecdsa.PrivateKey, backend *backends.SimulatedBackend) (common.Address, *rnode.Rnode) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	add, _, instance, err := rnode.DeployRnode(deployTransactor, backend)
	if err != nil {
		log.Fatal("DeployReward is error :", "error is", err)
	}
	return add, instance

}

func TestRNodeJoinRNode(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join rnode
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinRnode(candidateTransactOpts, initVersion)
	checkError(t, "join rnode", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidateAddr, true)

	checkRNodeNum(t, instance, 1)
}

func TestRNodeNotEnoughInvest(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join rnode
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(100000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinRnode(candidateTransactOpts, initVersion)
	checkError(t, "join rnode", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidateAddr, false)

	checkRNodeNum(t, instance, 0)
}

func TestRNodeJoinRNodeTwice(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join rnode
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinRnode(candidateTransactOpts, initVersion)
	checkError(t, "join rnode", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidateAddr, true)

	checkRNodeNum(t, instance, 1)

	_, err = instance.JoinRnode(candidateTransactOpts, initVersion)
	checkError(t, "join rnode", err)
	contractBackend.Commit()

	checkIsRNode(t, instance, candidateAddr, true)

	checkRNodeNum(t, instance, 1)
}

func TestRNodeMultiRNodes(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join rnode
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinRnode(candidateTransactOpts, initVersion)
	checkError(t, "join rnode", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidateAddr, true)

	checkRNodeNum(t, instance, 1)

	candidate2TransactOpts := bind.NewKeyedTransactor(candidate2Key)
	candidate2Invest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidate2TransactOpts.GasLimit = uint64(50000000)
	candidate2TransactOpts.Value = candidate2Invest
	_, err = instance.JoinRnode(candidate2TransactOpts, initVersion)
	checkError(t, "join rnode", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidate2Addr, true)

	checkRNodeNum(t, instance, 2)

	// get all rnodes
	addrs, err := instance.GetRnodes(nil)
	checkError(t, "get all rnodes", err)
	if addrs[0] != candidateAddr {
		t.Error("rnode 1 is not candidate 1")
	}
	if addrs[1] != candidate2Addr {
		t.Error("rnode 2 is not candidate 2")
	}
}

func TestJoinRNodeAndQuitRNode(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join rnode
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinRnode(candidateTransactOpts, initVersion)
	checkError(t, "join rnode", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidateAddr, true)

	checkRNodeNum(t, instance, 1)

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

	// quit rnode
	candidateTransactOpts = bind.NewKeyedTransactor(candidateKey)
	candidateInvest = new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err = instance.QuitRnode(candidateTransactOpts)
	checkError(t, "quit rnode", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidateAddr, false)

	checkRNodeNum(t, instance, 0)
}

func TestRNodeThreshold(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join rnode
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinRnode(candidateTransactOpts, initVersion)
	checkError(t, "join rnode", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidateAddr, true)

	checkRNodeNum(t, instance, 1)

	// set threshold = 1
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerInvest := new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	ownerTransactOpts.GasLimit = uint64(50000000)
	ownerTransactOpts.Value = ownerInvest

	newThreshold := new(big.Int).Mul(big.NewInt(3000000), big.NewInt(1e+18))
	_, err = instance.SetRnodeThreshold(ownerTransactOpts, newThreshold)
	checkError(t, "set rnode threshold", err)

	contractBackend.Commit()

	// get threshold
	threshold, err := instance.RnodeThreshold(nil)
	checkError(t, "get threshold", err)
	if threshold.Cmp(newThreshold) != 0 {
		t.Fatalf("threshold error! %d != %d", threshold, newThreshold)
	}

	// join rnode
	candidate2TransactOpts := bind.NewKeyedTransactor(candidate2Key)
	candidate2Invest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidate2TransactOpts.GasLimit = uint64(50000000)
	candidate2TransactOpts.Value = candidate2Invest
	_, err = instance.JoinRnode(candidate2TransactOpts, initVersion)
	checkError(t, "join rnode", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidate2Addr, false)

	checkRNodeNum(t, instance, 1)
}

func TestRNodeEnableAndDisable(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join rnode
	//candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	//candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	//candidateTransactOpts.GasLimit = uint64(50000000)
	//candidateTransactOpts.Value = candidateInvest
	//_, err := instance.JoinRnode(candidateTransactOpts, initVersion)
	//checkError(t, "join rnode", err)
	//
	//contractBackend.Commit()
	//
	//checkIsRNode(t, instance, candidateAddr, true)
	//
	//checkRNodeNum(t, instance, 1)

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

func TestRNodeWithSupportedVersion(t *testing.T) {
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:      {Balance: big.NewInt(1000000000000)},
		candidateAddr:  {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
		candidate2Addr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))}})
	_, instance := deploy(ownerKey, contractBackend)

	// join rnode
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err := instance.JoinRnode(candidateTransactOpts, initVersion)
	checkError(t, "join rnode", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidateAddr, true)

	checkRNodeNum(t, instance, 1)

	// set supportedVersion to 2
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerInvest := new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	ownerTransactOpts.GasLimit = uint64(50000000)
	ownerTransactOpts.Value = ownerInvest

	secondVersion := big.NewInt(2)
	_, err = instance.SetSupportedVersion(ownerTransactOpts, secondVersion)
	checkError(t, "set supported version", err)

	contractBackend.Commit()

	// join rnode with initVersion
	candidate2TransactOpts := bind.NewKeyedTransactor(candidate2Key)
	candidate2Invest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidate2TransactOpts.GasLimit = uint64(50000000)
	candidate2TransactOpts.Value = candidate2Invest
	_, err = instance.JoinRnode(candidate2TransactOpts, initVersion)
	checkError(t, "join rnode with init version", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidate2Addr, false)

	checkRNodeNum(t, instance, 1)

	// join rnode with secondVersion
	_, err = instance.JoinRnode(candidate2TransactOpts, secondVersion)
	checkError(t, "join rnode with second version", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidate2Addr, true)

	checkRNodeNum(t, instance, 2)
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

	// join rnode
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err = instance.JoinRnode(candidateTransactOpts, initVersion)
	checkError(t, "join rnode", err)

	contractBackend.Commit()

	state, err = contractBackend.Blockchain().State()

	amount2 := state.GetBalance(candidateAddr)

	if amount2.Cmp(amount1) >= 0 || new(big.Int).Add(amount2, candidateInvest).Cmp(amount1) >= 0 {
		t.Fatalf("balance error amount1: %v, amount2 + invest: %v", amount1, new(big.Int).Add(amount2, candidateInvest))
	}

	checkIsRNode(t, instance, candidateAddr, true)

	checkRNodeNum(t, instance, 1)

	// refund
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerInvest := new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	ownerTransactOpts.GasLimit = uint64(50000000)
	ownerTransactOpts.Value = ownerInvest

	_, err = instance.Refund(ownerTransactOpts, candidateAddr)
	checkError(t, "refund", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidateAddr, false)

	checkRNodeNum(t, instance, 0)

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

	// join rnode
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	_, err = instance.JoinRnode(candidateTransactOpts, initVersion)
	checkError(t, "join rnode", err)

	contractBackend.Commit()

	state, err = contractBackend.Blockchain().State()

	amount2 := state.GetBalance(candidateAddr)

	if amount2.Cmp(amount1) >= 0 || new(big.Int).Add(amount2, candidateInvest).Cmp(amount1) >= 0 {
		t.Fatalf("balance error amount1: %v, amount2 + invest: %v", amount1, new(big.Int).Add(amount2, candidateInvest))
	}

	checkIsRNode(t, instance, candidateAddr, true)

	checkRNodeNum(t, instance, 1)

	// refund all
	ownerTransactOpts := bind.NewKeyedTransactor(ownerKey)
	ownerInvest := new(big.Int).Mul(big.NewInt(0), big.NewInt(1e+18))
	ownerTransactOpts.GasLimit = uint64(50000000)
	ownerTransactOpts.Value = ownerInvest

	_, err = instance.RefundAll(ownerTransactOpts)
	checkError(t, "refund", err)

	contractBackend.Commit()

	checkIsRNode(t, instance, candidateAddr, false)

	checkRNodeNum(t, instance, 0)

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

func checkIsRNode(t *testing.T, instance *rnode.Rnode, addr common.Address, expect bool) {
	isRNode, err := instance.IsRnode(nil, addr)
	checkError(t, "is rnode", err)
	if isRNode != expect {
		t.Errorf("rnode check %v != %v", isRNode, expect)
	}
}

func checkRNodeNum(t *testing.T, instance *rnode.Rnode, amount int) {
	num, err := instance.GetRnodeNum(nil)
	checkError(t, "get rnodes num", err)

	if num.Cmp(new(big.Int).SetInt64(int64(amount))) != 0 {
		t.Errorf("rnode'num %d != %d", num, amount)
	}
}

func checkEnabled(t *testing.T, instance *rnode.Rnode, expect bool) {
	enabled, err := instance.Enabled(nil)
	checkError(t, "check enabled", err)

	if enabled != expect {
		t.Errorf("rnode'num %v != %v", enabled, expect)
	}
}
