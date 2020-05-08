package manager

import (
	"context"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	out "bitbucket.org/cpchain/chain/cmd/cpchain/campaign/output"
	"bitbucket.org/cpchain/chain/contracts/dpor/admission"
	"bitbucket.org/cpchain/chain/contracts/dpor/campaign"
	"bitbucket.org/cpchain/chain/contracts/dpor/rnode"
	"bitbucket.org/cpchain/chain/core"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	ownerKey, _              = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	ownerAddr                = crypto.PubkeyToAddress(ownerKey.PublicKey)
	cpuDifficulty     uint64 = 10
	memDifficulty     uint64 = 3
	cpuWorkTimeout    uint64 = 15
	memoryWorkTimeout uint64 = 15
)

func TestManager(t *testing.T) {
	t.Skip()
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	endPoint := "http://127.0.0.1:8503"
	kspath := "/Users/liaojinlong/.cpchain/keystore/"
	password := "/Users/liaojinlong/.cpchain/password"
	output := out.NewLogOutput()

	manager, _ := NewConsole(&ctx, endPoint, kspath, password, &output)

	manager.GetStatus()
}

func TestDeployCampaignContract(t *testing.T) {
	// backend
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{
		ownerAddr: {Balance: big.NewInt(1000000000000)},
	})
	// transactor
	deployTransactor := bind.NewKeyedTransactor(ownerKey)
	// deploy admission contract
	admissionAddr, _, _, err := admission.DeployAdmission(deployTransactor, contractBackend,
		new(big.Int).SetUint64(cpuDifficulty),
		new(big.Int).SetUint64(memDifficulty),
		new(big.Int).SetUint64(cpuWorkTimeout),
		new(big.Int).SetUint64(memoryWorkTimeout))
	if err != nil {
		t.Fatal(err)
	}
	contractBackend.Commit()

	// deploy rnode contract
	rnodeAddr, _, _, err := rnode.DeployRnode(deployTransactor, contractBackend)
	if err != nil {
		t.Fatal(err)
	}
	contractBackend.Commit()

	campaignAddr, _, _, err := campaign.DeployCampaign(deployTransactor, contractBackend, admissionAddr, rnodeAddr)
	if err != nil {
		t.Fatal(err)
	}
	_ = campaignAddr
	contractBackend.Commit()
}
