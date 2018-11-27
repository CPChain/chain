package rpt_test

import (
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts"
	"bitbucket.org/cpchain/chain/core"
	"crypto/ecdsa"
	"github.com/ethereum/go-ethereum/common"
	"math/big"
	"testing"
)

//
// var (
// 	key, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
// 	addr   = crypto.PubkeyToAddress(key.PublicKey)
// )

type rs struct {
	rptContract common.Address
	client      bind.ContractBackend
}

func deployrpt(prvKey *ecdsa.PrivateKey, backend *backends.SimulatedBackend) (common.Address, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	addr, _, _, err := dpor.DeployRpt(deployTransactor, backend)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
		return common.Address{}, err
	}
	backend.Commit()
	return addr, nil
}

func TestWindowsize(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	contractAddress, _ := deployrpt(key, contractBackend)
	contractBackend.Commit()
	rpt := rs{
		rptContract: contractAddress,
		client:      contractBackend,
	}
	instance, err := dpor.NewRpt(rpt.rptContract, rpt.client)
	if err != nil {
		log.Fatal("NewRpt is error", "error", err)
	}
	windowsze, err := instance.Window(nil)
	if err != nil {
		log.Fatal("windowsze is error", "error", err)
	}
	println("the window size is ", windowsze.Uint64())
}
