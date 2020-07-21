package rnode_test

import (
	"crypto/ecdsa"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor/rnode"
	RNode "bitbucket.org/cpchain/chain/contracts/dpor/rnode"
	"bitbucket.org/cpchain/chain/core"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	ownerKey, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	ownerAddr   = crypto.PubkeyToAddress(ownerKey.PublicKey)

	candidateKey, _ = crypto.HexToECDSA("8a1f9a8f95be41cd7ccb6168179afb4504aefe388d1e14474d32c45c72ce7b7a")
	candidateAddr   = crypto.PubkeyToAddress(candidateKey.PublicKey)

	initVersion = big.NewInt(1)
)

func deploy(prvKey *ecdsa.PrivateKey, backend *backends.SimulatedBackend) (common.Address, *RNode.Rnode) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	addr, _, instance, err := RNode.DeployRnode(deployTransactor, backend)
	if err != nil {
		log.Fatal("DeployReward is error :", "error is", err)
	}
	return addr, instance

}

func TestTNode(t *testing.T) {
	// create a chain which deployed rnode contract
	// deploy contract
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr:     {Balance: big.NewInt(1000000000000)},
		candidateAddr: {Balance: new(big.Int).Mul(big.NewInt(1000000), big.NewInt(configs.Cpc))},
	})
	address, instance := deploy(ownerKey, contractBackend)
	_ = address

	// insert rnode
	candidateTransactOpts := bind.NewKeyedTransactor(candidateKey)
	candidateInvest := new(big.Int).Mul(big.NewInt(200000), big.NewInt(1e+18))
	candidateTransactOpts.GasLimit = uint64(50000000)
	candidateTransactOpts.Value = candidateInvest
	if _, err := instance.JoinRnode(candidateTransactOpts, initVersion); err != nil {
		t.Fatal(err)
	}

	contractBackend.Commit()

	// new rnode interface which dpor engine needs
	service, _ := rnode.NewRNodeService(address, contractBackend)
	if rnodes, err := service.GetRNodes(); err != nil {
		t.Error(err)
	} else {
		if len(rnodes) != 1 {
			t.Errorf("expect rnode's length is 1, but got %v", len(rnodes))
		} else {
			if rnodes[0].Hex() != candidateAddr.Hex() {
				t.Errorf("expect the rnode 1 is %v, but got %v", candidateAddr.Hex(), rnodes[0].Hex())
			}
		}
	}

}
