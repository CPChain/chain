package contracts_test

import (
	"context"
	"crypto/ecdsa"
	"fmt"
	"math/big"
	"testing"

	contracts "bitbucket.org/cpchain/chain/contracts/dpor/rpt"
	"bitbucket.org/cpchain/chain/types"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/core"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	addresses = []common.Address{
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d86"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d85"),
	}
	key, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	addr   = crypto.PubkeyToAddress(key.PublicKey)
)

func deployRpt(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, *contracts.Rpt, *bind.TransactOpts, error) {
	Transactor := bind.NewKeyedTransactor(prvKey)
	rptAddr, _, rpt, err := contracts.DeployRpt(Transactor, backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	backend.Commit()
	return rptAddr, rpt, Transactor, nil
}

func TestRpt(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	contractAddr, rpt, opt, err := deployRpt(key, big.NewInt(0), contractBackend)
	checkError(t, "deploy contract: expected no error, got %v", err)

	// windowsize
	_ = contractAddr
	_ = opt
	window, err := rpt.Window(nil)
	checkError(t, "get window error", err)
	verifyEqual(t, window.Uint64(), uint64(100))

	// update windowsize
	_, err = rpt.UpdateWindow(opt, big.NewInt(int64(1)))
	checkError(t, "UpdateWindow error ", err)
	contractBackend.Commit()
	newWindow, err := rpt.Window(nil)
	verifyEqual(t, newWindow.Uint64(), uint64(1))

	// alpha
	alpha, err := rpt.Alpha(nil)
	checkError(t, "get alpha error", err)
	verifyEqual(t, alpha.Uint64(), uint64(50))

	// update updateAlpha
	_, err = rpt.UpdateAlpha(opt, big.NewInt(int64(1)))
	checkError(t, "UpdateAlpha error ", err)
	contractBackend.Commit()
	newAlpha, err := rpt.Window(nil)
	verifyEqual(t, newAlpha.Uint64(), uint64(1))

	// beta
	Beta, err := rpt.Beta(nil)
	checkError(t, "get beta error", err)
	verifyEqual(t, Beta.Uint64(), uint64(15))

	// update beta
	_, err = rpt.UpdateBeta(opt, big.NewInt(int64(1)))
	checkError(t, "UpdateBeta error ", err)
	contractBackend.Commit()
	newBeta, err := rpt.Beta(nil)
	verifyEqual(t, newBeta.Uint64(), uint64(1))

	// Gamma
	Gamma, err := rpt.Gamma(nil)
	checkError(t, "get Gamma error", err)
	verifyEqual(t, Gamma.Uint64(), uint64(10))

	// update Gamma
	_, err = rpt.UpdateGamma(opt, big.NewInt(int64(1)))
	checkError(t, "UpdateGamma error ", err)
	contractBackend.Commit()
	newGamma, err := rpt.Gamma(nil)
	verifyEqual(t, newGamma.Uint64(), uint64(1))

	// Psi
	Psi, err := rpt.Psi(nil)
	checkError(t, "get Psi error", err)
	verifyEqual(t, Psi.Uint64(), uint64(15))

	// update Psi
	_, err = rpt.UpdatePsi(opt, big.NewInt(int64(1)))
	checkError(t, "UpdatePsi error ", err)
	contractBackend.Commit()
	newPsi, err := rpt.Psi(nil)
	verifyEqual(t, newPsi.Uint64(), uint64(1))

	// Omega
	Omega, err := rpt.Omega(nil)
	checkError(t, "get Omega error", err)
	verifyEqual(t, Omega.Uint64(), uint64(10))

	// update Omega
	_, err = rpt.UpdateOmega(opt, big.NewInt(int64(1)))
	checkError(t, "UpdateOmega error ", err)
	contractBackend.Commit()
	newOmega, err := rpt.Omega(nil)
	verifyEqual(t, newOmega.Uint64(), uint64(1))

}

func TestUpdateElectionConfigs(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	contractAddr, rpt, opt, err := deployRpt(key, big.NewInt(0), contractBackend)
	checkError(t, "deploy contract: expected no error, got %v", err)

	_ = contractAddr
	_ = opt

	ownerTransactor := bind.NewKeyedTransactor(key)

	// success
	lowRptPercentage := new(big.Int).SetInt64(99)
	totalSeats := new(big.Int).SetInt64(7)
	lowRptSeats := new(big.Int).SetInt64(7)

	_, err = rpt.UpdateElectionConfigs(ownerTransactor, lowRptPercentage, totalSeats, lowRptSeats)
	checkError(t, "send tx: expected no error, got %v", err)
	contractBackend.Commit()

	lowRptPercentage1, err := rpt.LowRptPercentage(nil)
	if lowRptPercentage1.Cmp(lowRptPercentage) != 0 {
		t.Errorf("LowRptPercentage is error, expect %v but got %v", lowRptPercentage, lowRptPercentage1)
	}

	totalSeats1, err := rpt.TotalSeats(nil)
	if totalSeats1.Cmp(totalSeats1) != 0 {
		t.Errorf("TotalSeats is error, expect %v but got %v", totalSeats, totalSeats1)
	}

	lowRptSeats1, err := rpt.LowRptSeats(nil)
	if lowRptSeats.Cmp(lowRptSeats1) != 0 {
		t.Errorf("LowRptSeats is error, expect %v but got %v", lowRptSeats, lowRptSeats1)
	}

	// Fail1: lowRptPercentage > 100
	lowRptPercentage = new(big.Int).SetInt64(101)
	ownerTransactor.GasLimit = uint64(400000)
	tx, err := rpt.UpdateElectionConfigs(ownerTransactor, lowRptPercentage, totalSeats, lowRptSeats)
	checkError(t, "send tx: expected no error, got %v", err)
	contractBackend.Commit()

	receipt, _ := contractBackend.TransactionReceipt(context.Background(), tx.Hash())
	if receipt.Status != types.ReceiptStatusFailed {
		t.Fatal("the transaction should be failed but it is success!")
	}

	// Fail2: totalSeats > 8
	lowRptPercentage = new(big.Int).SetInt64(99)
	totalSeats = new(big.Int).SetInt64(9)
	ownerTransactor.GasLimit = uint64(400000)
	tx, err = rpt.UpdateElectionConfigs(ownerTransactor, lowRptPercentage, totalSeats, lowRptSeats)
	checkError(t, "send tx: expected no error, got %v", err)
	contractBackend.Commit()

	receipt, _ = contractBackend.TransactionReceipt(context.Background(), tx.Hash())
	if receipt.Status != types.ReceiptStatusFailed {
		t.Fatal("the transaction should be failed but it is success!")
	}

	// Fail3: totalSeats < lowRptSeats
	lowRptPercentage = new(big.Int).SetInt64(99)
	totalSeats = new(big.Int).SetInt64(5)
	lowRptSeats = new(big.Int).SetInt64(6)
	ownerTransactor.GasLimit = uint64(400000)
	tx, err = rpt.UpdateElectionConfigs(ownerTransactor, lowRptPercentage, totalSeats, lowRptSeats)
	checkError(t, "send tx: expected no error, got %v", err)
	contractBackend.Commit()

	receipt, _ = contractBackend.TransactionReceipt(context.Background(), tx.Hash())
	if receipt.Status != types.ReceiptStatusFailed {
		t.Fatal("the transaction should be failed but it is success!")
	}
}

func TestUpdateLowRptPercentage(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	contractAddr, rpt, opt, err := deployRpt(key, big.NewInt(0), contractBackend)
	checkError(t, "deploy contract: expected no error, got %v", err)

	_ = contractAddr
	_ = opt

	ownerTransactor := bind.NewKeyedTransactor(key)

	// success
	lowRptPercentage := new(big.Int).SetInt64(99)

	tx, err := rpt.UpdateLowRptPercentage(ownerTransactor, lowRptPercentage)
	checkError(t, "send tx: expected no error, got %v", err)

	contractBackend.Commit()

	receipt, _ := contractBackend.TransactionReceipt(context.Background(), tx.Hash())
	if receipt.Status == types.ReceiptStatusFailed {
		t.Fatal("the transaction should be success but failed!")
	}

	lowRptPercentage1, err := rpt.LowRptPercentage(nil)
	if lowRptPercentage1.Cmp(lowRptPercentage) != 0 {
		t.Errorf("LowRptPercentage is error, expect %v but got %v", lowRptPercentage, lowRptPercentage1)
	}

	// fail
	lowRptPercentage = new(big.Int).SetInt64(101)
	ownerTransactor.GasLimit = uint64(400000)

	tx, err = rpt.UpdateLowRptPercentage(ownerTransactor, lowRptPercentage)
	checkError(t, "send tx: expected no error, got %v", err)

	contractBackend.Commit()

	receipt, _ = contractBackend.TransactionReceipt(context.Background(), tx.Hash())
	if receipt.Status != types.ReceiptStatusFailed {
		t.Fatal("the transaction should be failed but suuccess!")
	}
}

func TestUpdateTotalSeats(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	contractAddr, rpt, opt, err := deployRpt(key, big.NewInt(0), contractBackend)
	checkError(t, "deploy contract: expected no error, got %v", err)

	_ = contractAddr
	_ = opt

	ownerTransactor := bind.NewKeyedTransactor(key)

	// success
	totalSeats := new(big.Int).SetInt64(7)

	tx, err := rpt.UpdateTotalSeats(ownerTransactor, totalSeats)
	checkError(t, "send tx: expected no error, got %v", err)

	contractBackend.Commit()

	receipt, _ := contractBackend.TransactionReceipt(context.Background(), tx.Hash())
	if receipt.Status == types.ReceiptStatusFailed {
		t.Fatal("the transaction should be success but failed!")
	}

	totalSeats1, err := rpt.TotalSeats(nil)
	if totalSeats1.Cmp(totalSeats) != 0 {
		t.Errorf("TotalSeats is error, expect %v but got %v", totalSeats, totalSeats1)
	}

	// fail
	totalSeats = new(big.Int).SetInt64(9)
	ownerTransactor.GasLimit = uint64(400000)

	tx, err = rpt.UpdateTotalSeats(ownerTransactor, totalSeats)
	checkError(t, "send tx: expected no error, got %v", err)

	contractBackend.Commit()

	receipt, _ = contractBackend.TransactionReceipt(context.Background(), tx.Hash())
	if receipt.Status != types.ReceiptStatusFailed {
		t.Fatal("the transaction should be failed but suuccess!")
	}
}

func TestUpdateLowRptSeats(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	contractAddr, rpt, opt, err := deployRpt(key, big.NewInt(0), contractBackend)
	checkError(t, "deploy contract: expected no error, got %v", err)

	_ = contractAddr
	_ = opt

	ownerTransactor := bind.NewKeyedTransactor(key)

	// success
	lowRptSeats := new(big.Int).SetInt64(7)

	tx, err := rpt.UpdateLowRptSeats(ownerTransactor, lowRptSeats)
	checkError(t, "send tx: expected no error, got %v", err)

	contractBackend.Commit()

	receipt, _ := contractBackend.TransactionReceipt(context.Background(), tx.Hash())
	if receipt.Status == types.ReceiptStatusFailed {
		t.Fatal("the transaction should be success but failed!")
	}

	lowRptSeats1, err := rpt.LowRptSeats(nil)
	if lowRptSeats1.Cmp(lowRptSeats) != 0 {
		t.Errorf("LowRptSeats is error, expect %v but got %v", lowRptSeats, lowRptSeats1)
	}

	// fail
	lowRptSeats = new(big.Int).SetInt64(9)
	ownerTransactor.GasLimit = uint64(400000)

	tx, err = rpt.UpdateLowRptSeats(ownerTransactor, lowRptSeats)
	checkError(t, "send tx: expected no error, got %v", err)

	contractBackend.Commit()

	receipt, _ = contractBackend.TransactionReceipt(context.Background(), tx.Hash())
	if receipt.Status != types.ReceiptStatusFailed {
		t.Fatal("the transaction should be failed but suuccess!")
	}
}

func verifyEqual(t *testing.T, v1 uint64, v2 uint64) {
	fmt.Println("v1,v2 is :", v1, v2)
	if v1 != v2 {
		t.Fatal("not equal!", "v1 is :", v1, "v2 is :", v2)
	}
}

func checkError(t *testing.T, msg string, err error) {
	if err != nil {
		t.Fatalf(msg, err)
	}
}
