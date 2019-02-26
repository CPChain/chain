package common

import (
	"context"
	"crypto/ecdsa"
	"testing"

	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/reward"

	"bitbucket.org/cpchain/chain/api/cpclient"
	"github.com/ethereum/go-ethereum/common"
)

func buildClient(ctx *context.Context, t *testing.T) (*cpclient.Client, *ecdsa.PrivateKey, *ecdsa.PublicKey, common.Address) {
	// endPoint := "http://3.0.61.106:8523"
	endPoint := "http://54.169.196.149:8503"
	keyStoreFilePath := "/Users/liaojinlong/.cpchain/keystore1/"
	// password := "password"
	password := "2163607794_4042"
	client, privateKey, publicKeyECDSA, fromAddress, err := NewCpcClient(endPoint, keyStoreFilePath, password)
	if err != nil {
		t.Fatal(err.Error())
	}
	return client, privateKey, publicKeyECDSA, fromAddress
}

func checkError(t *testing.T, err error) {
	if err != nil {
		t.Fatal(err)
	}
}

func TestNewCpcClient(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	client, _, _, fromAddress := buildClient(&ctx, t)
	balance, err := client.BalanceAt(ctx, fromAddress, nil)
	if err != nil {
		t.Error(err)
	}
	t.Log("Balance", balance)
}

func TestContractExist(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	client, _, _, _ := buildClient(&ctx, t)
	contracts := map[string]common.Address{
		"ContractReward":    common.HexToAddress("0x94576e35a55D6BbF9bB45120bC835a668557eF42"),
		"ContractCampaign":  common.HexToAddress("0x1404Bf355428523F8e51E68Df00A0521e413F98E"),
		"ContractAdmission": common.HexToAddress("0x8f01875F462CBBc956CB9C0392dE6053A31C9C99"),
	}
	for name, addr := range contracts {
		code, err := client.CodeAt(ctx, addr, nil)
		if len(code) > 0 {
			t.Log("contract " + name + " code exist")
		} else {
			t.Log("contract " + name + " code not exist")
		}
		if err != nil {
			t.Error("DeployContract failed: " + name)
		}
	}
}

func TestReward(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	client, _, _, fromAddress := buildClient(&ctx, t)
	addr := common.HexToAddress("0x94576e35a55D6BbF9bB45120bC835a668557eF42")
	instance, err := reward.NewReward(addr, client)
	if err != nil {
		t.Error(err)
	}
	// GetFreeBalance
	freeBalance, err := instance.GetFreeBalance(nil, fromAddress)
	checkError(t, err)
	t.Log("FreeBalance:", freeBalance)
	// GetLockedBalance
	lockedBalance, err := instance.GetLockedBalance(nil, fromAddress)
	checkError(t, err)
	t.Log("LockedBalance:", lockedBalance)

	// IsParticipant
	isParticipant, err := instance.IsParticipant(nil, fromAddress)
	checkError(t, err)
	t.Log("IsParticipant", isParticipant)

	n, err := instance.BonusPool(nil)
	checkError(t, err)
	t.Log(n)

	// SubmitDeposit
	_, err = instance.SubmitDeposit(nil)
	checkError(t, err)

	// ISRNode
	isRNode, err := instance.IsRNode(nil, fromAddress)
	checkError(t, err)
	t.Log("IsRNode", isRNode)

}

func TestStatus(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	client, _, _, _ := buildClient(&ctx, t)
	contracts := map[string]common.Address{
		"ContractReward":    common.HexToAddress("0x94576e35a55D6BbF9bB45120bC835a668557eF42"),
		"ContractCampaign":  common.HexToAddress("0x1404Bf355428523F8e51E68Df00A0521e413F98E"),
		"ContractAdmission": common.HexToAddress("0x8f01875F462CBBc956CB9C0392dE6053A31C9C99"),
	}
	// Admission Control

	// Miner
	_, err := campaign.NewCampaign(contracts["ContractCampaign"], client)
	checkError(t, err)

	// RNode
	// see TestReward.

	// Proposer
}
